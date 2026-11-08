import Langlands.Representation.Category.NoetherianClosure
import Langlands.Representation.Filtration.Definitions
import Langlands.Representation.Exponents.FullParabolicLeviFunctors
import Langlands.Representation.Exponents.LeviInductionFiniteTypeStatement
import Langlands.Representation.Exponents.LeviJacquetFiniteTypeStatement
import Langlands.Representation.Geometric.RepresentedGeometricLemmaStatement
import Langlands.Representation.Exponents.SmoothRepNoetherianReduction
import Langlands.Representation.Exponents.LeviInductionNoSupercuspidalSubquotientStatement
import Langlands.Representation.Category.IrreducibleSubquotientExistence

/-! # Renard VI.7.5, Theorem, from explicit inputs

The VI.7.5 Theorem (normalized parabolic induction preserves finite type) is reduced, by
strong induction on the Lie dimension of `G`, to five published or stated inputs: the
VI.7.5 Proposition, the represented geometric lemma (VI.5.1), Renard VI.1.3, the objectwise
cuspidal/remainder splitting (VI.3.5) and a finite proper-parabolic supercuspidality test.
None of the inputs is proved here.
-/

noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj MonoidAlgebra

namespace Langlands.NoetherianRepresentation

universe uC vC uR uG uH uV

variable {k : Type uR} [CommRing k] {G : Type uG} [Monoid G]

/-- A natural finite filtration of a functor to representations, evaluated at one object:
if every graded piece at `X` is Noetherian, so is the value at `X`. -/
theorem of_repFunctorFiltration {C : Type uC} [Category.{vC} C] {F : C ⥤ Rep.{uV} k G}
    {n : ℕ} (s : RepFunctorFiltration F n) (X : C)
    (hgr : ∀ i, _root_.IsNoetherian k[G] ((s.graded i).obj X).ρ.asModule) :
    _root_.IsNoetherian k[G] (F.obj X).ρ.asModule :=
  of_objectRepFiltration
    (ObjectRepFiltration.ofSubrepresentations (A := F.obj X) (fun i => (s.step i).obj X)
      (s.monotone X) (s.zero X) (s.top X)) hgr

/-- A functor glued, in Bernstein–Zelevinsky's sense, from finitely many functors to
representations: if every piece at `X` is Noetherian, so is the value at `X`. -/
theorem of_isGluedFrom {C : Type uC} [Category.{vC} C] {F : C ⥤ Rep.{uV} k G}
    {n : ℕ} {pieces : Fin n → C ⥤ Rep.{uV} k G} (h : IsGluedFrom F pieces) (X : C)
    (hp : ∀ i, _root_.IsNoetherian k[G] ((pieces i).obj X).ρ.asModule) :
    _root_.IsNoetherian k[G] (F.obj X).ρ.asModule := by
  obtain ⟨e, s, hs⟩ := h
  refine of_repFunctorFiltration s X fun i => ?_
  obtain ⟨φ⟩ := hs i
  have : _root_.IsNoetherian k[G] (((pieces ∘ e) i).obj X).ρ.asModule := hp (e i)
  exact of_equiv (Representation.equivOfIso (φ.app X)).symm

/-- Finite generation does not change under pullback along a surjective monoid
homomorphism: both group-algebra modules have the same submodule lattice. -/
theorem finite_comp_surjective_iff {V : Type uV} [AddCommGroup V] [Module k V]
    {H : Type uH} [Monoid H] (ρ : Representation k G V) (f : H →* G)
    (hf : Function.Surjective f) :
    Module.Finite k[G] ρ.asModule ↔ Module.Finite k[H] (Representation.asModule (ρ.comp f)) := by
  let e := compSubmoduleOrderIso ρ f hf
  have hspan : ∀ S : Set V, e (Submodule.span k[G] (show Set ρ.asModule from S)) =
      Submodule.span k[H] (show Set (Representation.asModule (ρ.comp f)) from S) := by
    intro S
    apply le_antisymm
    · rw [← e.le_symm_apply, Submodule.span_le]
      intro v hv
      exact (mem_compSubmoduleOrderIso ρ f hf _ v).mp
        (by rw [e.apply_symm_apply]; exact Submodule.subset_span hv)
    · rw [Submodule.span_le]
      intro v hv
      exact (mem_compSubmoduleOrderIso ρ f hf _ v).mpr (Submodule.subset_span hv)
  rw [Module.finite_def, Module.finite_def, Submodule.fg_def, Submodule.fg_def]
  constructor
  · rintro ⟨S, hS, hspanS⟩
    refine ⟨S, hS, ?_⟩
    have h := hspan S
    rw [hspanS, e.map_top] at h
    exact h.symm
  · rintro ⟨S, hS, hspanS⟩
    refine ⟨S, hS, ?_⟩
    apply e.injective
    have h := hspan S
    rw [hspanS] at h
    rw [h, e.map_top]

end Langlands.NoetherianRepresentation

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

universe u v

/-- Renard VI.7.5, Theorem, for one connected reductive group `G` over `k`: the body of
`LeviInductionFiniteTypeStatement` with `k` and `G` fixed. -/
def LeviInductionFiniteTypeAt (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G) : Prop :=
  haveI := hG.isAffineHom
  letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
    (P M U : GroupScheme (Spec (CommRingCat.of k)))
    (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
    (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hmul : IsIso (subgroupMultiplication l r)),
    haveI := hl.isConnectedReductive.isAffineHom
    letI : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
    haveI : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
    haveI : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
    ∀ (ρ : SmoothRep.{0, u, v} ℂ (rationalPoints M)),
      Module.Finite (MonoidAlgebra ℂ (rationalPoints M)) ρ.representation.asModule →
        Module.Finite (MonoidAlgebra ℂ (rationalPoints G))
          ((leviInductionFunctor.{u, v} p l r hp hr hl hmul).obj ρ).representation.asModule

/-- The VI.7.5 Theorem is the per-group statement for every field and group. -/
theorem leviInductionFiniteTypeStatement_iff :
    LeviInductionFiniteTypeStatement.{u, v} ↔
      ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
        [IsNonarchimedeanLocalField k] [T2Space k]
        (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
        LeviInductionFiniteTypeAt.{u, v} k G hG :=
  Iff.rfl

section FullParabolic

variable {k : Type u} [Field k] [TopologicalSpace k] [T2Space k]
  {G P M U : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance leviInductionFiniteTypeStepsAmbientTopology :
    TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]

/-- Renard VI.7.5, Theorem, for the full parabolic `P = G`: normalized induction is
transport along the Levi-point isomorphism `M(F) ≃ G(F)`, so it preserves finite
generation. -/
theorem leviInduction_finite_of_isIso (p : P ⟶ G) [IsIso p] (l : M ⟶ P)
    (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
    (hG : IsConnectedReductive G) (r : U ⟶ P)
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hmul : IsIso (subgroupMultiplication l r))
    (σ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M))
    (hσ : letI := leviPointTopology l hl
      Module.Finite (MonoidAlgebra ℂ (rationalPoints M)) σ.representation.asModule) :
    letI := leviPointTopology l hl
    Module.Finite (MonoidAlgebra ℂ (rationalPoints G))
      ((leviInductionFunctor p l r hp hr hl hmul).obj σ).representation.asModule := by
  let := leviPointTopology l hl
  let e := fullParabolicLeviPointsEquiv p l hp hl hG
  have h := (NoetherianRepresentation.finite_comp_surjective_iff σ.representation
    e.symm.toMonoidHom e.symm.surjective).mp hσ
  let φ := (fullParabolicLeviInductionEquiv p l hp hl hG r hr hmul σ).symm
  exact Module.Finite.of_surjective
    (Representation.IntertwiningMap.equivLinearMapAsModule _ _ φ.toIntertwiningMap)
    φ.toLinearEquiv.surjective

end FullParabolic

section Pieces

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance leviInductionFiniteTypePiecesAmbientTopology :
    TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {P M N Q L U : GroupScheme (Spec (CommRingCat.of k))}
  {p : P ⟶ G} {l : M ⟶ P} {r : N ⟶ P} {hp : IsParabolicSubgroup p}
  {hr : LeviSubgroup.IsGeometricUnipotentRadical r} {hl : IsRationalLeviSubgroup l}
  {hmul : IsIso (subgroupMultiplication l r)}
  {q : Q ⟶ G} {lQ : L ⟶ Q} {rQ : U ⟶ Q} {hq : IsParabolicSubgroup q}
  {hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ} {hlQ : IsRationalLeviSubgroup lQ}
  {hmulQ : IsIso (subgroupMultiplication lQ rQ)} {z : rationalPoints G}

/-- A geometric-lemma piece `i^L_{Q'} ∘ ι ∘ r^M_{P'}` of a finitely generated `ρ` is finitely
generated, given Renard VI.1.3 (`LeviJacquetFiniteTypeStatement`) and the VI.7.5 Theorem for
the group `L`. -/
theorem GeometricLemmaIntersectionDatum.finite_pieceFunctor_obj
    (hJ : LeviJacquetFiniteTypeStatement.{u, v})
    (D : GeometricLemmaIntersectionDatum p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ z)
    (hL : LeviInductionFiniteTypeAt.{u, v} k L hlQ.isConnectedReductive)
    (ρ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M))
    (hρ : letI := leviPointTopology l hl
      Module.Finite (MonoidAlgebra ℂ (rationalPoints M)) ρ.representation.asModule) :
    Module.Finite (MonoidAlgebra ℂ (rationalPoints L)) (D.pieceFunctor.obj ρ).ρ.asModule := by
  have := hl.isConnectedReductive.isAffineHom
  have := hlQ.isConnectedReductive.isAffineHom
  let := leviPointTopology l hl
  let := leviPointTopology lQ hlQ
  have := leviPoints_locallyCompactSpace p l hp hl
  have := leviPoints_nonarchimedeanGroup p l hp hl
  have := leviPoints_locallyCompactSpace q lQ hq hlQ
  have := leviPoints_nonarchimedeanGroup q lQ hq hlQ
  let := leviPointTopology D.l' D.hl'
  let := leviPointTopology D.lQ' D.hlQ'
  have h1 := hJ k M hl.isConnectedReductive D.P' D.M' D.N' D.p' D.l' D.r' D.hp' D.hl' D.hr'
    D.hmul' ρ hρ
  have h2 := (NoetherianRepresentation.finite_comp_surjective_iff
    ((leviJacquetFunctor D.p' D.l' D.r' D.hp' D.hr' D.hl' D.hmul').obj ρ).representation
    D.e.toMonoidHom D.e.surjective).mp h1
  exact hL D.Q' D.L' D.U' D.q' D.lQ' D.rQ' D.hq' D.hlQ' D.hrQ' D.hmulQ'
    (SmoothRep.pullback D.e ((leviJacquetFunctor D.p' D.l' D.r' D.hp' D.hr' D.hl' D.hmul').obj ρ))
    h2

end Pieces

section JacquetOfInduction

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance leviInductionFiniteTypeJacquetAmbientTopology :
    TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {P M N Q L U : GroupScheme (Spec (CommRingCat.of k))}

/-- Let `P = MN` and `Q = LU` be actual rational parabolics of `G` and `ρ` a finitely
generated smooth representation of `M(F)`. Assume the represented geometric lemma, Renard
VI.1.3, the VI.7.5 Theorem for `L`, and that finitely generated smooth representations of
`L(F)` (carrier universe `max u v`) are Noetherian. Then `r_Q^G i_P^G ρ` is Noetherian over
`ℂ[L(F)]`: it is glued from finitely many pieces `i^L_{Q'}(ι(r^M_{P'} ρ))`, each finitely
generated and hence Noetherian. -/
theorem leviJacquet_leviInduction_isNoetherian_of_geometricLemma
    (hGeom : RepresentedGeometricLemmaStatement.{u, v})
    (hJ : LeviJacquetFiniteTypeStatement.{u, v})
    (hG : IsConnectedReductive G)
    (p : P ⟶ G) (l : M ⟶ P) (r : N ⟶ P)
    (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hmul : IsIso (subgroupMultiplication l r))
    (q : Q ⟶ G) (lQ : L ⟶ Q) (rQ : U ⟶ Q)
    (hq : IsParabolicSubgroup q) (hlQ : IsRationalLeviSubgroup lQ)
    (hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ)
    (hmulQ : IsIso (subgroupMultiplication lQ rQ))
    (hL : LeviInductionFiniteTypeAt.{u, v} k L hlQ.isConnectedReductive)
    (hNoethL : letI := leviPointTopology lQ hlQ
      ∀ σ : SmoothRep.{0, u, max u v} ℂ (rationalPoints L),
        Module.Finite (MonoidAlgebra ℂ (rationalPoints L)) σ.representation.asModule →
          _root_.IsNoetherian (MonoidAlgebra ℂ (rationalPoints L)) σ.representation.asModule)
    (ρ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M))
    (hρ : letI := leviPointTopology l hl
      Module.Finite (MonoidAlgebra ℂ (rationalPoints M)) ρ.representation.asModule) :
    haveI := hlQ.isConnectedReductive.isAffineHom
    letI := leviPointTopology l hl
    letI := leviPointTopology lQ hlQ
    haveI := leviPoints_locallyCompactSpace q lQ hq hlQ
    haveI := leviPoints_nonarchimedeanGroup q lQ hq hlQ
    _root_.IsNoetherian (MonoidAlgebra ℂ (rationalPoints L))
      ((leviJacquetFunctor.{u, max u v} q lQ rQ hq hrQ hlQ hmulQ).obj
        ((leviInductionFunctor p l r hp hr hl hmul).obj ρ)).representation.asModule := by
  have := hl.isConnectedReductive.isAffineHom
  have := hlQ.isConnectedReductive.isAffineHom
  let := leviPointTopology l hl
  let := leviPointTopology lQ hlQ
  have := leviPoints_locallyCompactSpace q lQ hq hlQ
  have := leviPoints_nonarchimedeanGroup q lQ hq hlQ
  obtain ⟨m, c, z, -, D, hglue⟩ :=
    hGeom k G hG P M N Q L U p l r hp hl hr hmul q lQ rQ hq hlQ hrQ hmulQ
  exact NoetherianRepresentation.of_isGluedFrom hglue ρ fun i =>
    hNoethL _ ((D i).finite_pieceFunctor_obj hJ hL ρ hρ)

end JacquetOfInduction

section CuspidalPart

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance leviInductionFiniteTypeReductionAmbientTopology :
    TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {P M U : GroupScheme (Spec (CommRingCat.of k))}

/-- Assuming Renard VI.5.2 (`LeviInductionNoSupercuspidalSubquotientStatement`), the
supercuspidal part of a normalized induction from a proper parabolic is zero: a nonzero
supercuspidal part would have an irreducible subquotient, which would be a supercuspidal
irreducible subquotient of the induction. -/
theorem isZero_cuspidalPartFunctor_obj_leviInduction
    (hNoSc : LeviInductionNoSupercuspidalSubquotientStatement.{u, v})
    (hG : IsConnectedReductive G)
    (hs : ∀ A : SmoothRep.{0, u, max u v} ℂ (rationalPoints G),
      HasCuspidalRemainderSplitting A)
    (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
    (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hmul : IsIso (subgroupMultiplication l r)) (hproper : ¬ IsIso p)
    (ρ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M)) :
    IsZero ((cuspidalPartFunctor hs).obj
      ((leviInductionFunctor p l r hp hr hl hmul).obj ρ)) := by
  let := leviPointTopology l hl
  let X := (leviInductionFunctor p l r hp hr hl hmul).obj ρ
  let C := (cuspidalPartFunctor hs).obj X
  rw [SmoothRep.isZero_iff_subsingleton]
  by_contra hC
  rw [not_subsingleton_iff_nontrivial] at hC
  obtain ⟨D, hirr, hDC⟩ := SmoothRep.exists_isIrreducible_isSubquotient_of_nontrivial C
  have hscD : IsSupercuspidal D :=
    IsSupercuspidal.of_isSubquotient hDC (isSupercuspidal_cuspidalPartFunctor_obj hs X)
  have hDX : SmoothRep.IsSubquotient D X := by
    obtain ⟨C', i, q, hi, hq⟩ := SmoothRep.isSubquotient_iff_exists.mp hDC
    have hι : Function.Injective (SmoothRep.hom ((cuspidalPartι hs).app X)) :=
      (SmoothRep.mono_iff_injective _).mp inferInstance
    exact SmoothRep.isSubquotient_iff_exists.mpr ⟨C', i ≫ (cuspidalPartι hs).app X, q,
      fun a b h => hi (hι h), hq⟩
  exact hNoSc k G hG P M U p l r hp hl hr hmul hproper ρ D hirr hDX hscD

end CuspidalPart

section Reduction

attribute [local instance] PointGroup.group PointGroup.topology

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]

/-- The inductive step: if the VI.7.5 Theorem holds for the Levi of every proper parabolic
of `G`, it holds for `G`, given the explicit inputs. -/
theorem leviInductionFiniteTypeAt_of_levis
    (hProp : SmoothRepNoetherianCategoryStatement.{u, max u v})
    (hGeom : RepresentedGeometricLemmaStatement.{u, v})
    (h1 : LeviJacquetFiniteTypeStatement.{u, v})
    (h2 : RepresentedCuspidalRemainderSplittingStatement.{u, max u v})
    (h4 : FiniteProperParabolicSupercuspidalTestStatement.{u, max u v})
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)
    (ih : ∀ (P M : GroupScheme (Spec (CommRingCat.of k))) (p : P ⟶ G) (l : M ⟶ P),
      IsParabolicSubgroup p → ∀ hl : IsRationalLeviSubgroup l, ¬ IsIso p →
        LeviInductionFiniteTypeAt.{u, v} k M hl.isConnectedReductive) :
    LeviInductionFiniteTypeAt.{u, v} k G hG := by
  have := hG.isAffineHom
  let _ : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  unfold LeviInductionFiniteTypeAt
  intro _ _ P M U p l r hp hl hr hmul ρ hρ
  by_cases hiso : IsIso p
  · exact leviInduction_finite_of_isIso p l hp hl hG r hr hmul ρ hρ
  let := leviPointTopology l hl
  let X := (leviInductionFunctor p l r hp hr hl hmul).obj ρ
  have hNoSc := leviInductionNoSupercuspidalSubquotient_of_cuspidalRemainderSplitting h2
  have hs := h2 k G hG
  obtain ⟨n, D, hDp, htest⟩ := h4 k G hG
  have := familyFunctor_preservesMonomorphisms D hs hG
  have hX : Langlands.Renard.IsNoetherianObject X := by
    refine Langlands.Renard.noetherianObject_of_finite_family (familyFunctor D hs)
      (familyFunctor_jointlyReflectsMonoIsos D hs hG htest) X fun j => ?_
    cases j with
    | none =>
      have h0 := isZero_cuspidalPartFunctor_obj_leviInduction hNoSc hG hs p l r hp hl hr hmul
        hiso ρ
      have : Subsingleton ((cuspidalPartFunctor hs).obj X).representation.asModule :=
        (SmoothRep.isZero_iff_subsingleton _).mp h0
      have hN : _root_.IsNoetherian (MonoidAlgebra ℂ (rationalPoints G))
          ((cuspidalPartFunctor hs).obj X).representation.asModule := inferInstance
      exact (SmoothRep.renardNoetherian_iff _).mpr hN
    | some i =>
      let := leviPointTopology (D i).l (D i).hl
      have := leviPoints_locallyCompactSpace (D i).p (D i).l (D i).hp (D i).hl
      have := leviPoints_nonarchimedeanGroup (D i).p (D i).l (D i).hp (D i).hl
      have hM : Langlands.Renard.IsNoetherianCategory
          (SmoothRep.{0, u, max u v} ℂ (rationalPoints (D i).M)) :=
        hProp k (D i).M (D i).hl.isConnectedReductive
      apply (SmoothRep.renardNoetherian_iff _).mpr
      exact leviJacquet_leviInduction_isNoetherian_of_geometricLemma hGeom h1 hG
        p l r hp hl hr hmul (D i).p (D i).l (D i).r (D i).hp (D i).hl (D i).hr (D i).hmul
        (ih (D i).P (D i).M (D i).p (D i).l (D i).hp (D i).hl (hDp i))
        (fun σ hσ => (SmoothRep.renardNoetherian_iff σ).mp
          (hM.2 σ ((SmoothRep.renardFiniteType_iff σ).mpr hσ)))
        ρ hρ
  have := (SmoothRep.renardNoetherian_iff X).mp hX
  infer_instance

/-- Renard VI.7.5, Theorem, from explicit inputs: the Proposition (at carrier universe
`max u v`), the represented geometric lemma VI.5.1, Renard VI.1.3, the objectwise
cuspidal/remainder splitting of VI.3.5, and a finite proper-parabolic supercuspidality
test. The proof is by strong induction on the Lie dimension of `G`. -/
theorem leviInductionFiniteType_of_inputs
    (hProp : SmoothRepNoetherianCategoryStatement.{u, max u v})
    (hGeom : RepresentedGeometricLemmaStatement.{u, v})
    (h1 : LeviJacquetFiniteTypeStatement.{u, v})
    (h2 : RepresentedCuspidalRemainderSplittingStatement.{u, max u v})
    (h4 : FiniteProperParabolicSupercuspidalTestStatement.{u, max u v}) :
    LeviInductionFiniteTypeStatement.{u, v} := by
  intro k _ _ _ _ _ G hG
  show LeviInductionFiniteTypeAt.{u, v} k G hG
  suffices key : ∀ (d : ℕ) (G : GroupScheme (Spec (CommRingCat.of k)))
      (hG : IsConnectedReductive G), @Lie.dimension k _ G hG.isAffineHom = d →
        LeviInductionFiniteTypeAt.{u, v} k G hG from
    @key _ G hG rfl
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro G hG hd
    refine leviInductionFiniteTypeAt_of_levis hProp hGeom h1 h2 h4 G hG
      fun P M p l hp hl hproper => ?_
    exact ih _ ((lieDimension_levi_lt hG p l hp hl hproper).trans_eq hd) M
      hl.isConnectedReductive rfl

end Reduction

end Langlands.Aubert.General.RepresentedParabolic
