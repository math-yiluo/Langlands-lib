import Langlands.Representation.Exponents.MaximalLeviSupercuspidalLeviExponentStatements
import Langlands.Representation.Exponents.MaximalLeviSupercuspidalLengthTwoStatement
import Langlands.Representation.Exponents.MaximalLeviExponentTransport
import Langlands.Representation.Exponents.MaximalLeviFixedDirectionNormalizer
import Langlands.Representation.Exponents.LeviParabolicFunctorsExactProof
import Langlands.Representation.Exponents.JacquetNontrivialityTransfer
import Langlands.Representation.Geometric.LeviConjugatePiece
import Langlands.Representation.Filtration.ScalarGradedOccurrences
import Langlands.GroupScheme.Rational.CenterSplitComponentCompactnessStatement
import Langlands.GroupScheme.Rational.ParabolicAmbientTransport

/-! # The good constituent of Renard VII.1.3 from the geometric lemma

Let `P = MN` be an actual maximal proper rational parabolic, `ρ` an irreducible supercuspidal
representation of `M(F)` whose central character is not unitary, and suppose that `i_P^G ρ` is
reducible with a unitary central character. By the length-two statement there is a short
exact sequence `π₁ ↪ i_P^G ρ ↠ π₂` with `π₁, π₂` irreducible. This module proves that `π₁` or
`π₂` has its exponents along every parabolic with Levi factor `M` in the positive cones,
assuming the represented geometric lemma, the length-two statement, the cone complement
statement for maximal Levi subgroups, the self-normalizing property of parabolics and the
compactness of the centre modulo a split component.

If both were bad, the bad exponents would come from full pieces of the geometric lemma, so
they are conjugates `ω_A ∘ e` of the restriction `ω_A` of the central character of `ρ`.
Conjugating the two parabolics moves both bad exponents to `ω_A` itself, with real part
outside both transported cones; the cone complement statement then makes the two
parabolics equal. So `ω_A` is an exponent of `π₁` and of `π₂` along one parabolic `Q`, and
the two-grade lemma gives two distinct pieces of `r_Q i_P^G ρ` on which the split component
acts by `ω_A`. The fixed-direction lemma puts both double-coset representatives in `Q(F)`,
so the two pieces coincide.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj

namespace Langlands

namespace ScalarGraded

variable {k : Type*} [Field k] {Γ : Type*} [Monoid Γ] {V W : Type*} [AddCommGroup V]
  [Module k V] [AddCommGroup W] [Module k W] {ρ : Representation k Γ V}
  {σ : Representation k Γ W}

/-- An intertwining map commutes with every power of `ρ(g) - c`. -/
theorem intertwiningMap_pow_sub_smul_apply (T : ρ.IntertwiningMap σ) (g : Γ) (c : k) (d : ℕ)
    (v : V) : ((σ g - c • 1) ^ d) (T v) = T (((ρ g - c • 1) ^ d) v) := by
  induction d generalizing v with
  | zero => simp only [pow_zero, Module.End.one_apply]
  | succ d ih =>
    rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ← ih]
    congr 1
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub,
      map_smul, T.isIntertwining]

end ScalarGraded

namespace RepFunctorFiltration

variable {k : Type*} [Field k] {Γ : Type*} [Group Γ] {C : Type*} [Category C]
  {F : C ⥤ Rep k Γ} {n : ℕ} (s : RepFunctorFiltration F n) (X : C)
  {R : Fin n → Rep k Γ} (e : ∀ i, (s.graded i).obj X ≅ R i)
  {B : Type*} [Group B] {κ : B →* Γ} {c : Fin n → B → k}
  (hR : ScalarGraded.ZeroOrScalarIrreducible R κ c)
  {V W : Type*} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  {σ₁ : Representation k Γ V} {σ₂ : Representation k Γ W}

include s e hR in
/-- A generalized eigencharacter of a representation embedded in `F.obj X` is the scalar
character of a nonzero graded piece. -/
theorem exists_grade_of_injective (T : σ₁.IntertwiningMap (F.obj X).ρ)
    (hT : Function.Injective T) (χ : B →* kˣ) (hχ : IsGeneralizedEigencharacter (σ₁.comp κ) χ) :
    ∃ i, Nontrivial (R i) ∧ c i = fun t => (χ t : k) := by
  obtain ⟨d, v, hv, hgen⟩ := (isGeneralizedEigencharacter_iff _ χ).mp hχ
  refine s.exists_grade_of_pow_apply_eq_zero X e hR (fun t => (χ t : k)) d (v := T v) ?_ ?_
  · intro h
    exact hv (hT (h.trans (map_zero T).symm))
  · intro t
    rw [ScalarGraded.intertwiningMap_pow_sub_smul_apply]
    have h := hgen t
    rw [MonoidHom.comp_apply] at h
    rw [h, map_zero]

include s e hR in
/-- A generalized eigencharacter of a quotient representation of `F.obj X` is the scalar
character of a nonzero graded piece. -/
theorem exists_grade_of_surjective (T : (F.obj X).ρ.IntertwiningMap σ₂)
    (hT : Function.Surjective T) (χ : B →* kˣ)
    (hχ : IsGeneralizedEigencharacter (σ₂.comp κ) χ) :
    ∃ i, Nontrivial (R i) ∧ c i = fun t => (χ t : k) := by
  obtain ⟨d, v, hv, hgen⟩ := (isGeneralizedEigencharacter_iff _ χ).mp hχ
  obtain ⟨w, rfl⟩ := hT v
  refine s.exists_grade_of_pow_apply_mem X e hR T.ker (fun t => (χ t : k)) d (w := w) ?_ ?_
  · exact fun h => hv ((Representation.IntertwiningMap.mem_ker _ _ T w).mp h)
  · intro t
    rw [Representation.IntertwiningMap.mem_ker, ← ScalarGraded.intertwiningMap_pow_sub_smul_apply]
    have h := hgen t
    rw [MonoidHom.comp_apply] at h
    exact h

include s e hR in
/-- If a common generalized eigencharacter occurs in a subrepresentation of `F.obj X` and in
the corresponding quotient, it is the scalar character of two distinct nonzero graded
pieces. -/
theorem exists_two_grades_of_comp_eq_zero (T₁ : σ₁.IntertwiningMap (F.obj X).ρ)
    (T₂ : (F.obj X).ρ.IntertwiningMap σ₂) (hT₁ : Function.Injective T₁)
    (hT₂ : Function.Surjective T₂) (hT : ∀ v, T₂ (T₁ v) = 0) (χ : B →* kˣ)
    (hχ₁ : IsGeneralizedEigencharacter (σ₁.comp κ) χ)
    (hχ₂ : IsGeneralizedEigencharacter (σ₂.comp κ) χ) :
    ∃ i j, i ≠ j ∧ Nontrivial (R i) ∧ Nontrivial (R j) ∧ c i = (fun t => (χ t : k)) ∧
      c j = fun t => (χ t : k) := by
  obtain ⟨d, v, hv, hgen⟩ := (isGeneralizedEigencharacter_iff _ χ).mp hχ₁
  obtain ⟨d', v', hv', hgen'⟩ := (isGeneralizedEigencharacter_iff _ χ).mp hχ₂
  obtain ⟨w, rfl⟩ := hT₂ v'
  refine s.exists_two_grades X e hR T₂.ker (fun t => (χ t : k)) (d := d) (d' := d')
    (v := T₁ v) ?_ (hT v) ?_ (w := w) ?_ ?_
  · intro h
    exact hv (hT₁ (h.trans (map_zero T₁).symm))
  · intro t
    rw [ScalarGraded.intertwiningMap_pow_sub_smul_apply]
    have h := hgen t
    rw [MonoidHom.comp_apply] at h
    rw [h, map_zero]
  · exact fun h => hv' ((Representation.IntertwiningMap.mem_ker _ _ T₂ w).mp h)
  · intro t
    rw [Representation.IntertwiningMap.mem_ker, ← ScalarGraded.intertwiningMap_pow_sub_smul_apply]
    have h := hgen' t
    rw [MonoidHom.comp_apply] at h
    exact h

end RepFunctorFiltration

end Langlands

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme RealTorusSpace

section Constituent

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance maximalLeviConstituentAmbientPointTopology :
    TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {P M N Q U : GroupScheme (Spec (CommRingCat.of k))}
  {p : P ⟶ G} {l : M ⟶ P} {r : N ⟶ P} {hp : IsParabolicSubgroup p}
  {hr : LeviSubgroup.IsGeometricUnipotentRadical r} {hl : IsRationalLeviSubgroup l}
  {hmul : IsIso (subgroupMultiplication l r)}
  {q : Q ⟶ G} {lQ : M ⟶ Q} {rQ : U ⟶ Q} {hq : IsParabolicSubgroup q}
  {hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ} {hlQ : IsRationalLeviSubgroup lQ}
  {hmulQ : IsIso (subgroupMultiplication lQ rQ)}
  {n : ℕ} {z : Fin n → rationalPoints G}
  (D : ∀ i, GeometricLemmaIntersectionDatum p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ (z i))

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
/-- **Scalars of the pieces.** For a parabolic `Q` with Levi factor `M` and the same Levi
composite as `P`, and a supercuspidal irreducible `ρ` on which the split component `a` acts
by `ω_A`, every piece of the geometric lemma is zero, or irreducible with `a` acting by a
scalar character `c i`; for a nonzero piece, `c i = ω_A ∘ e` for a lift `e : A ≅ A` of an
automorphism of `M` that is conjugation by the double-coset representative. -/
theorem exists_zeroOrScalarIrreducible_pieces (hcomp : lQ ≫ q = l ≫ p)
    (ρ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M))
    (hirr : letI := leviPointTopology l hl; ρ.IsIrreducible)
    (hsuper : haveI := hl.isConnectedReductive.isAffineHom
      letI := leviPointTopology l hl
      haveI := leviPoints_locallyCompactSpace p l hp hl
      haveI := leviPoints_nonarchimedeanGroup p l hp hl
      ∀ (P' M' U' : GroupScheme (Spec (CommRingCat.of k)))
        (p' : P' ⟶ M) (l' : M' ⟶ P') (r' : U' ⟶ P')
        (hp' : IsParabolicSubgroup p') (hl' : IsRationalLeviSubgroup l')
        (hr' : LeviSubgroup.IsGeometricUnipotentRadical r')
        (hmul' : IsIso (subgroupMultiplication l' r')),
        ¬ IsIso p' → Subsingleton ((jacquetFunctor p' l' r' hp' hr' hl' hmul').obj ρ))
    {A : CommGroupScheme (Spec (CommRingCat.of k))} {a : A.toGrp ⟶ M}
    (ha : IsSplitComponent a) (ωA : rationalPoints A.toGrp →* ℂˣ)
    (hωA : letI := leviPointTopology l hl; ∀ (t : rationalPoints A.toGrp) (y : ρ),
      ρ.representation (rationalPoints.map a t) y = (ωA t : ℂ) • y) :
    ∃ c : Fin n → rationalPoints A.toGrp → ℂ,
      ScalarGraded.ZeroOrScalarIrreducible (fun i => (D i).pieceFunctor.obj ρ)
        (rationalPoints.map a) c ∧
      ∀ i, Nontrivial ((D i).pieceFunctor.obj ρ) → ∃ (ψ : M ≅ M) (e : A ≅ A),
        ψ.hom ≫ l ≫ p = l ≫ p ≫ (G.innerIso (z i)).hom ∧
        CommGroupScheme.groupHom e.hom ≫ a = a ≫ ψ.hom ∧
        c i = fun t => (ωA (rationalPoints.map (CommGroupScheme.groupHom e.hom) t) : ℂ) := by
  have key : ∀ i, ∃ c : rationalPoints A.toGrp → ℂ,
      (Subsingleton ((D i).pieceFunctor.obj ρ) ∨
        (((D i).pieceFunctor.obj ρ).ρ.IsIrreducible ∧ ∀ t (y : (D i).pieceFunctor.obj ρ),
          ((D i).pieceFunctor.obj ρ).ρ (rationalPoints.map a t) y = c t • y)) ∧
      (Nontrivial ((D i).pieceFunctor.obj ρ) → ∃ (ψ : M ≅ M) (e : A ≅ A),
        ψ.hom ≫ l ≫ p = l ≫ p ≫ (G.innerIso (z i)).hom ∧
        CommGroupScheme.groupHom e.hom ≫ a = a ≫ ψ.hom ∧
        c = fun t => (ωA (rationalPoints.map (CommGroupScheme.groupHom e.hom) t) : ℂ)) := by
    intro i
    rcases (D i).subsingleton_or_isIrreducible_scalar hcomp ρ hirr hsuper ha ωA hωA with
      h | ⟨-, hirr', ψ, e, hψ, he, hs⟩
    · exact ⟨fun _ => 1, Or.inl h, fun hn => absurd h (not_subsingleton_iff_nontrivial.mpr hn)⟩
    · exact ⟨fun t => (ωA (rationalPoints.map (CommGroupScheme.groupHom e.hom) t) : ℂ),
        Or.inr ⟨hirr', hs⟩, fun _ => ⟨ψ, e, hψ, he, rfl⟩⟩
  choose c hc using key
  exact ⟨c, fun i => (hc i).1, fun i hn => (hc i).2 hn⟩

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
/-- **Locating an exponent of a subrepresentation.** If `r_Q` of `f : W ⟶ i_P ρ` is
injective, every exponent of `W` along `Q` is `ω_A ∘ e` for a lift `e` of an automorphism of
`M` that is conjugation by a double-coset representative. -/
theorem exists_conjugation_of_injective
    (hglue : IsGluedFrom
      (leviJacquetInductionFunctor.{u, v} p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ)
      (fun i => (D i).pieceFunctor))
    (hcomp : lQ ≫ q = l ≫ p)
    (ρ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M))
    (hirr : letI := leviPointTopology l hl; ρ.IsIrreducible)
    (hsuper : haveI := hl.isConnectedReductive.isAffineHom
      letI := leviPointTopology l hl
      haveI := leviPoints_locallyCompactSpace p l hp hl
      haveI := leviPoints_nonarchimedeanGroup p l hp hl
      ∀ (P' M' U' : GroupScheme (Spec (CommRingCat.of k)))
        (p' : P' ⟶ M) (l' : M' ⟶ P') (r' : U' ⟶ P')
        (hp' : IsParabolicSubgroup p') (hl' : IsRationalLeviSubgroup l')
        (hr' : LeviSubgroup.IsGeometricUnipotentRadical r')
        (hmul' : IsIso (subgroupMultiplication l' r')),
        ¬ IsIso p' → Subsingleton ((jacquetFunctor p' l' r' hp' hr' hl' hmul').obj ρ))
    {A : CommGroupScheme (Spec (CommRingCat.of k))} {a : A.toGrp ⟶ M}
    (ha : IsSplitComponent a) (ωA : rationalPoints A.toGrp →* ℂˣ)
    (hωA : letI := leviPointTopology l hl; ∀ (t : rationalPoints A.toGrp) (y : ρ),
      ρ.representation (rationalPoints.map a t) y = (ωA t : ℂ) • y)
    {W : SmoothRep.{0, u, max u v} ℂ (rationalPoints G)}
    (f : W ⟶ (leviInductionFunctor p l r hp hr hl hmul).obj ρ)
    (hf : letI := leviPointTopology lQ hlQ; Function.Injective
      (SmoothRep.hom ((leviJacquetFunctor q lQ rQ hq hrQ hlQ hmulQ).map f)))
    (χ : rationalPoints A.toGrp →* ℂˣ)
    (hχ : IsNormalizedJacquetExponent q lQ rQ hq hlQ hrQ hmulQ ha W χ) :
    ∃ (i : Fin n) (ψ : M ≅ M) (e : A ≅ A), ψ.hom ≫ l ≫ p = l ≫ p ≫ (G.innerIso (z i)).hom ∧
      CommGroupScheme.groupHom e.hom ≫ a = a ≫ ψ.hom ∧
      χ = ωA.comp (rationalPoints.map (CommGroupScheme.groupHom e.hom)) := by
  let := leviPointTopology l hl
  obtain ⟨c, hZ, hc⟩ := exists_zeroOrScalarIrreducible_pieces D hcomp ρ hirr hsuper ha ωA hωA
  obtain ⟨π, s, hs⟩ := hglue
  have iso : ∀ i, (s.graded i).obj ρ ≅ (D (π i)).pieceFunctor.obj ρ :=
    fun i => (hs i).some.app ρ
  have hZ' : ScalarGraded.ZeroOrScalarIrreducible (fun i => (D (π i)).pieceFunctor.obj ρ)
      (rationalPoints.map a) (fun i => c (π i)) := fun i => hZ (π i)
  have hχ' := (isNormalizedJacquetExponent_iff_leviJacquet q lQ rQ hq hlQ hrQ hmulQ ha W χ).mp hχ
  obtain ⟨i, hi, hci⟩ := RepFunctorFiltration.exists_grade_of_injective s ρ iso hZ'
    (SmoothRep.hom ((leviJacquetFunctor q lQ rQ hq hrQ hlQ hmulQ).map f)) hf χ hχ'
  obtain ⟨ψ, e, hψ, he, hce⟩ := hc (π i) hi
  refine ⟨π i, ψ, e, hψ, he, MonoidHom.ext fun t => Units.ext ?_⟩
  exact congrFun (hci.symm.trans hce) t

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
/-- **Locating an exponent of a quotient.** If `r_Q` of `g : i_P ρ ⟶ W` is surjective, every
exponent of `W` along `Q` is `ω_A ∘ e` for a lift `e` of an automorphism of `M` that is
conjugation by a double-coset representative. -/
theorem exists_conjugation_of_surjective
    (hglue : IsGluedFrom
      (leviJacquetInductionFunctor.{u, v} p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ)
      (fun i => (D i).pieceFunctor))
    (hcomp : lQ ≫ q = l ≫ p)
    (ρ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M))
    (hirr : letI := leviPointTopology l hl; ρ.IsIrreducible)
    (hsuper : haveI := hl.isConnectedReductive.isAffineHom
      letI := leviPointTopology l hl
      haveI := leviPoints_locallyCompactSpace p l hp hl
      haveI := leviPoints_nonarchimedeanGroup p l hp hl
      ∀ (P' M' U' : GroupScheme (Spec (CommRingCat.of k)))
        (p' : P' ⟶ M) (l' : M' ⟶ P') (r' : U' ⟶ P')
        (hp' : IsParabolicSubgroup p') (hl' : IsRationalLeviSubgroup l')
        (hr' : LeviSubgroup.IsGeometricUnipotentRadical r')
        (hmul' : IsIso (subgroupMultiplication l' r')),
        ¬ IsIso p' → Subsingleton ((jacquetFunctor p' l' r' hp' hr' hl' hmul').obj ρ))
    {A : CommGroupScheme (Spec (CommRingCat.of k))} {a : A.toGrp ⟶ M}
    (ha : IsSplitComponent a) (ωA : rationalPoints A.toGrp →* ℂˣ)
    (hωA : letI := leviPointTopology l hl; ∀ (t : rationalPoints A.toGrp) (y : ρ),
      ρ.representation (rationalPoints.map a t) y = (ωA t : ℂ) • y)
    {W : SmoothRep.{0, u, max u v} ℂ (rationalPoints G)}
    (g : (leviInductionFunctor p l r hp hr hl hmul).obj ρ ⟶ W)
    (hg : letI := leviPointTopology lQ hlQ; Function.Surjective
      (SmoothRep.hom ((leviJacquetFunctor q lQ rQ hq hrQ hlQ hmulQ).map g)))
    (χ : rationalPoints A.toGrp →* ℂˣ)
    (hχ : IsNormalizedJacquetExponent q lQ rQ hq hlQ hrQ hmulQ ha W χ) :
    ∃ (i : Fin n) (ψ : M ≅ M) (e : A ≅ A), ψ.hom ≫ l ≫ p = l ≫ p ≫ (G.innerIso (z i)).hom ∧
      CommGroupScheme.groupHom e.hom ≫ a = a ≫ ψ.hom ∧
      χ = ωA.comp (rationalPoints.map (CommGroupScheme.groupHom e.hom)) := by
  let := leviPointTopology l hl
  obtain ⟨c, hZ, hc⟩ := exists_zeroOrScalarIrreducible_pieces D hcomp ρ hirr hsuper ha ωA hωA
  obtain ⟨π, s, hs⟩ := hglue
  have iso : ∀ i, (s.graded i).obj ρ ≅ (D (π i)).pieceFunctor.obj ρ :=
    fun i => (hs i).some.app ρ
  have hZ' : ScalarGraded.ZeroOrScalarIrreducible (fun i => (D (π i)).pieceFunctor.obj ρ)
      (rationalPoints.map a) (fun i => c (π i)) := fun i => hZ (π i)
  have hχ' := (isNormalizedJacquetExponent_iff_leviJacquet q lQ rQ hq hlQ hrQ hmulQ ha W χ).mp hχ
  obtain ⟨i, hi, hci⟩ := RepFunctorFiltration.exists_grade_of_surjective s ρ iso hZ'
    (SmoothRep.hom ((leviJacquetFunctor q lQ rQ hq hrQ hlQ hmulQ).map g)) hg χ hχ'
  obtain ⟨ψ, e, hψ, he, hce⟩ := hc (π i) hi
  refine ⟨π i, ψ, e, hψ, he, MonoidHom.ext fun t => Units.ext ?_⟩
  exact congrFun (hci.symm.trans hce) t

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
/-- **Uniqueness of the piece.** Let `ω_A` be an exponent along `Q` of both ends of a short
exact sequence `W₁ ↪ i_P ρ ↠ W₂` that stays exact under `r_Q`. If every point `w` whose
inner automorphism normalizes `M` through a lift `e` with `ω_A ∘ e = ω_A` lies in `Q(F)`,
this is impossible: two distinct pieces would carry `ω_A`, and both of their double-coset
representatives would lie in `Q(F)`. -/
theorem false_of_isNormalizedJacquetExponent_of_isShortExact
    (hglue : IsGluedFrom
      (leviJacquetInductionFunctor.{u, v} p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ)
      (fun i => (D i).pieceFunctor))
    (cc : Fin n ≃ DoubleCoset.Quotient (pointImage p : Set (rationalPoints G))
      (pointImage q : Set (rationalPoints G)))
    (hz : ∀ i, DoubleCoset.mk (pointImage p) (pointImage q) (z i) = cc i)
    (hcomp : lQ ≫ q = l ≫ p)
    (ρ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M))
    (hirr : letI := leviPointTopology l hl; ρ.IsIrreducible)
    (hsuper : haveI := hl.isConnectedReductive.isAffineHom
      letI := leviPointTopology l hl
      haveI := leviPoints_locallyCompactSpace p l hp hl
      haveI := leviPoints_nonarchimedeanGroup p l hp hl
      ∀ (P' M' U' : GroupScheme (Spec (CommRingCat.of k)))
        (p' : P' ⟶ M) (l' : M' ⟶ P') (r' : U' ⟶ P')
        (hp' : IsParabolicSubgroup p') (hl' : IsRationalLeviSubgroup l')
        (hr' : LeviSubgroup.IsGeometricUnipotentRadical r')
        (hmul' : IsIso (subgroupMultiplication l' r')),
        ¬ IsIso p' → Subsingleton ((jacquetFunctor p' l' r' hp' hr' hl' hmul').obj ρ))
    {A : CommGroupScheme (Spec (CommRingCat.of k))} {a : A.toGrp ⟶ M}
    (ha : IsSplitComponent a) (ωA : rationalPoints A.toGrp →* ℂˣ)
    (hωA : letI := leviPointTopology l hl; ∀ (t : rationalPoints A.toGrp) (y : ρ),
      ρ.representation (rationalPoints.map a t) y = (ωA t : ℂ) • y)
    (hmem : ∀ (w : rationalPoints G) (ψ : M ≅ M) (e : A ≅ A),
      ψ.hom ≫ l ≫ p = l ≫ p ≫ (G.innerIso w).hom →
      CommGroupScheme.groupHom e.hom ≫ a = a ≫ ψ.hom →
      ωA.comp (rationalPoints.map (CommGroupScheme.groupHom e.hom)) = ωA → w ∈ pointImage q)
    {W₁ W₂ : SmoothRep.{0, u, max u v} ℂ (rationalPoints G)}
    (f : W₁ ⟶ (leviInductionFunctor p l r hp hr hl hmul).obj ρ)
    (g : (leviInductionFunctor p l r hp hr hl hmul).obj ρ ⟶ W₂)
    (hex : letI := leviPointTopology lQ hlQ; SmoothRep.IsShortExact
      (SmoothRep.hom ((leviJacquetFunctor q lQ rQ hq hrQ hlQ hmulQ).map f))
      (SmoothRep.hom ((leviJacquetFunctor q lQ rQ hq hrQ hlQ hmulQ).map g)))
    (h₁ : IsNormalizedJacquetExponent q lQ rQ hq hlQ hrQ hmulQ ha W₁ ωA)
    (h₂ : IsNormalizedJacquetExponent q lQ rQ hq hlQ hrQ hmulQ ha W₂ ωA) : False := by
  let := leviPointTopology l hl
  obtain ⟨c, hZ, hc⟩ := exists_zeroOrScalarIrreducible_pieces D hcomp ρ hirr hsuper ha ωA hωA
  obtain ⟨π, s, hs⟩ := hglue
  have iso : ∀ i, (s.graded i).obj ρ ≅ (D (π i)).pieceFunctor.obj ρ :=
    fun i => (hs i).some.app ρ
  have hZ' : ScalarGraded.ZeroOrScalarIrreducible (fun i => (D (π i)).pieceFunctor.obj ρ)
      (rationalPoints.map a) (fun i => c (π i)) := fun i => hZ (π i)
  have h₁' := (isNormalizedJacquetExponent_iff_leviJacquet q lQ rQ hq hlQ hrQ hmulQ ha W₁ ωA).mp h₁
  have h₂' := (isNormalizedJacquetExponent_iff_leviJacquet q lQ rQ hq hlQ hrQ hmulQ ha W₂ ωA).mp h₂
  have hT : ∀ v, SmoothRep.hom ((leviJacquetFunctor q lQ rQ hq hrQ hlQ hmulQ).map g)
      (SmoothRep.hom ((leviJacquetFunctor q lQ rQ hq hrQ hlQ hmulQ).map f) v) = 0 := by
    intro v
    have hv := LinearMap.mem_range_self
      (SmoothRep.hom ((leviJacquetFunctor q lQ rQ hq hrQ hlQ hmulQ).map f)).toLinearMap v
    rw [hex.2.2, LinearMap.mem_ker] at hv
    exact hv
  obtain ⟨i, j, hij, hi, hj, hci, hcj⟩ := RepFunctorFiltration.exists_two_grades_of_comp_eq_zero
    s ρ iso hZ' (SmoothRep.hom ((leviJacquetFunctor q lQ rQ hq hrQ hlQ hmulQ).map f))
    (SmoothRep.hom ((leviJacquetFunctor q lQ rQ hq hrQ hlQ hmulQ).map g)) hex.1 hex.2.1 hT ωA
    h₁' h₂'
  have key : ∀ i, Nontrivial ((D (π i)).pieceFunctor.obj ρ) →
      c (π i) = (fun t => (ωA t : ℂ)) →
      cc (π i) = DoubleCoset.mk (pointImage p) (pointImage q) 1 := by
    intro i hi hci
    obtain ⟨ψ, e, hψ, he, hce⟩ := hc (π i) hi
    have hω : ωA.comp (rationalPoints.map (CommGroupScheme.groupHom e.hom)) = ωA :=
      MonoidHom.ext fun t => Units.ext (congrFun (hce.symm.trans hci) t)
    have hzq := hmem (z (π i)) ψ e hψ he hω
    rw [← hz (π i)]
    exact DoubleCoset.eq.mpr ⟨1, one_mem _, (z (π i))⁻¹, inv_mem hzq, by simp⟩
  exact hij (π.injective (cc.injective ((key i hi hci).trans (key j hj hcj).symm)))

end Constituent

/-- The constituent step of Renard VII.1.3 as a consequence of the represented geometric
lemma, the length-two statement, the cone complement statement for maximal Levi subgroups,
the self-normalizing property of parabolics and the compactness of the centre modulo a
split component. -/
def MaximalLeviSupercuspidalLeviPositiveConstituentReductionStatement : Prop :=
  RepresentedGeometricLemmaStatement.{u, v} →
    MaximalLeviSupercuspidalInductionLengthTwoStatement.{u, v} →
      MaximalLeviConeComplementStatement.{u} →
        ParabolicSelfNormalizerStatement.{u} →
          CenterSplitComponentCompactnessStatement.{u} →
            MaximalLeviSupercuspidalLeviPositiveConstituentStatement.{u, v}

/-- **Renard VII.1.3, constituent step.** The represented geometric lemma, the length-two
statement, the cone complement statement, the self-normalizing property of parabolics and
the compactness of the centre modulo a split component give an irreducible sub or quotient
of `i_P^G ρ` whose exponents along every parabolic with Levi factor `M` are positive. -/
theorem maximalLeviSupercuspidalLeviPositiveConstituent_of_geometricLemma :
    MaximalLeviSupercuspidalLeviPositiveConstituentReductionStatement.{u, v} := by
  intro hgeo hlen hcone hnorm hcpt k _ _ _ _ _ G hG
  have := hG.isAffineHom
  have := hG.smooth
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ P M N p l r hp hl hr hmul hpG hmax
  have := hl.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
  have : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
  have : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
  intro ρ hirr hsuper hnu hred hunit
  obtain ⟨cπ⟩ := hunit
  obtain ⟨π₁, π₂, h₁, h₂, f, g, hses⟩ :=
    hlen k G hG P M N p l r hp hl hr hmul hpG hmax ρ hirr hsuper hred
  by_cases H₁ : HasPositiveLeviJacquetExponents (l ≫ p) π₁
  · exact ⟨π₁, h₁, H₁, Or.inl ⟨f, hses.1⟩⟩
  refine ⟨π₂, h₂, ?_, Or.inr ⟨g, hses.2.1⟩⟩
  intro Q₂ U₂ A₂ q₂ lQ₂ rQ₂ a₂ hq₂ hlQ₂ hrQ₂ hmulQ₂ ha₂ pres₂ χ₂ hc₂ hχ₂
  by_contra hn₂
  apply H₁
  intro Q₁ U₁ A₁ q₁ lQ₁ rQ₁ a₁ hq₁ hlQ₁ hrQ₁ hmulQ₁ ha₁ pres₁ χ₁ hc₁ hχ₁
  by_contra hn₁
  -- The central character of `ρ` and its restriction `ωA` to the split component `a₁`.
  obtain ⟨ω, hω⟩ := exists_hasCentralCharacter_of_isIrreducible l hl ρ hirr
  obtain ⟨ωA, hωAdef⟩ : ∃ ωA, ωA = splitComponentCentralCharacter a₁ ha₁ ω := ⟨_, rfl⟩
  have hωA : ∀ (t : rationalPoints A₁.toGrp) (y : ρ),
      ρ.representation (rationalPoints.map a₁ t) y = (ωA t : ℂ) • y := by
    intro t y
    rw [hωAdef]
    exact splitComponentCentralCharacter_smul ha₁ ρ ω hω t y
  obtain ⟨ε, hε⟩ := IsSplitComponent.exists_iso_comp ha₂ ha₁ (Iso.refl M)
  have hε' : CommGroupScheme.groupHom ε.hom ≫ a₁ = a₂ := by
    simpa only [Iso.refl_hom, Category.comp_id] using hε
  have hωA₂ : ∀ (t : rationalPoints A₂.toGrp) (y : ρ),
      ρ.representation (rationalPoints.map a₂ t) y =
        ((ωA.comp (rationalPoints.map (CommGroupScheme.groupHom ε.hom))) t : ℂ) • y := by
    intro t y
    rw [← hε', pointMap_comp_apply]
    exact hωA _ y
  -- Locate both bad exponents in full pieces of the geometric lemma.
  have hex₁ := (leviParabolicFunctorsExact.{u, max u v} k G hG Q₁ M U₁ q₁ lQ₁ rQ₁ hq₁ hlQ₁ hrQ₁
    hmulQ₁).2 f g hses
  have hex₂ := (leviParabolicFunctorsExact.{u, max u v} k G hG Q₂ M U₂ q₂ lQ₂ rQ₂ hq₂ hlQ₂ hrQ₂
    hmulQ₂).2 f g hses
  obtain ⟨m₁, -, z₁, -, D₁, hglue₁⟩ :=
    hgeo k G hG P M N Q₁ M U₁ p l r hp hl hr hmul q₁ lQ₁ rQ₁ hq₁ hlQ₁ hrQ₁ hmulQ₁
  obtain ⟨i₁, ψ₁, e₁, hψ₁, he₁, hχ₁e⟩ := exists_conjugation_of_injective D₁ hglue₁ hc₁ ρ hirr
    hsuper ha₁ ωA hωA f hex₁.1 χ₁ hχ₁
  obtain ⟨m₂, -, z₂, -, D₂, hglue₂⟩ :=
    hgeo k G hG P M N Q₂ M U₂ p l r hp hl hr hmul q₂ lQ₂ rQ₂ hq₂ hlQ₂ hrQ₂ hmulQ₂
  obtain ⟨i₂, ψ₂, e₂', hψ₂, he₂', hχ₂e'⟩ := exists_conjugation_of_surjective D₂ hglue₂ hc₂ ρ hirr
    hsuper ha₂ _ hωA₂ g hex₂.2.1 χ₂ hχ₂
  obtain ⟨e₂, he₂, hχ₂e⟩ : ∃ e₂ : A₂ ≅ A₁, CommGroupScheme.groupHom e₂.hom ≫ a₁ = a₂ ≫ ψ₂.hom ∧
      χ₂ = ωA.comp (rationalPoints.map (CommGroupScheme.groupHom e₂.hom)) := by
    refine ⟨e₂' ≪≫ ε, ?_, ?_⟩
    · change (CommGroupScheme.groupHom e₂'.hom ≫ CommGroupScheme.groupHom ε.hom) ≫ a₁ = _
      rw [Category.assoc, hε', he₂']
    · rw [hχ₂e']
      refine MonoidHom.ext fun t => ?_
      simp only [MonoidHom.comp_apply]
      congr 1
  -- Conjugate both parabolics so that the bad exponents become `ωA`.
  have hq₁' : IsParabolicSubgroup (q₁ ≫ (G.innerIso (z₁ i₁)).hom) := hq₁.comp_iso _
  have hlQ₁' : IsRationalLeviSubgroup (ψ₁.symm.hom ≫ lQ₁) := hlQ₁.iso_comp ψ₁.symm
  have hmulQ₁' : IsIso (subgroupMultiplication (ψ₁.symm.hom ≫ lQ₁) rQ₁) :=
    isIso_subgroupMultiplication_iso_comp ψ₁.symm hmulQ₁
  have hc₁' : (ψ₁.symm.hom ≫ lQ₁) ≫ q₁ ≫ (G.innerIso (z₁ i₁)).hom = l ≫ p := by
    change (ψ₁.inv ≫ lQ₁) ≫ q₁ ≫ (G.innerIso (z₁ i₁)).hom = l ≫ p
    rw [Category.assoc, ← Category.assoc lQ₁, hc₁, Category.assoc, ← hψ₁,
      Iso.inv_hom_id_assoc]
  have hq₂' : IsParabolicSubgroup (q₂ ≫ (G.innerIso (z₂ i₂)).hom) := hq₂.comp_iso _
  have hlQ₂' : IsRationalLeviSubgroup (ψ₂.symm.hom ≫ lQ₂) := hlQ₂.iso_comp ψ₂.symm
  have hmulQ₂' : IsIso (subgroupMultiplication (ψ₂.symm.hom ≫ lQ₂) rQ₂) :=
    isIso_subgroupMultiplication_iso_comp ψ₂.symm hmulQ₂
  have hc₂' : (ψ₂.symm.hom ≫ lQ₂) ≫ q₂ ≫ (G.innerIso (z₂ i₂)).hom = l ≫ p := by
    change (ψ₂.inv ≫ lQ₂) ≫ q₂ ≫ (G.innerIso (z₂ i₂)).hom = l ≫ p
    rw [Category.assoc, ← Category.assoc lQ₂, hc₂, Category.assoc, ← hψ₂,
      Iso.inv_hom_id_assoc]
  have hE₁ : IsNormalizedJacquetExponent (q₁ ≫ (G.innerIso (z₁ i₁)).hom) (ψ₁.symm.hom ≫ lQ₁)
      rQ₁ hq₁' hlQ₁' hrQ₁ hmulQ₁' ha₁ π₁ ωA :=
    (isNormalizedJacquetExponent_conjugate_iff q₁ lQ₁ rQ₁ hq₁ hlQ₁ hrQ₁ hmulQ₁ (z₁ i₁) ψ₁ e₁ he₁
      hq₁' hlQ₁' hmulQ₁' ha₁ ha₁ π₁ ωA).mpr (hχ₁e ▸ hχ₁)
  have hE₂ : IsNormalizedJacquetExponent (q₂ ≫ (G.innerIso (z₂ i₂)).hom) (ψ₂.symm.hom ≫ lQ₂)
      rQ₂ hq₂' hlQ₂' hrQ₂ hmulQ₂' ha₁ π₂ ωA :=
    (isNormalizedJacquetExponent_conjugate_iff q₂ lQ₂ rQ₂ hq₂ hlQ₂ hrQ₂ hmulQ₂ (z₂ i₂) ψ₂ e₂ he₂
      hq₂' hlQ₂' hmulQ₂' ha₂ ha₁ π₂ ωA).mpr (hχ₂e ▸ hχ₂)
  have hopen : @IsOpen _ (RationalPointFamily.splitComponentPointTopology ha₁)
      (ωA.ker : Set (rationalPoints A₁.toGrp)) :=
    ((isNormalizedJacquetExponent_iff_isOpen_ker_and _ _ _ _ _ _ _ ha₁ π₁ ωA).mp hE₁).1
  have hn₁' := normalizedRealPart_notMem_positiveCone_conjugate q₁ pres₁ ha₁ (z₁ i₁) ψ₁ e₁ ha₁
    he₁ ωA hopen (hχ₁e ▸ hn₁)
  have hn₂' := normalizedRealPart_notMem_positiveCone_conjugate q₂ pres₂ ha₂ (z₂ i₂) ψ₂ e₂ ha₁
    he₂ ωA hopen (hχ₂e ▸ hn₂)
  -- The real part of `ωA` is a nonzero direction vanishing on the centre of `G`.
  have hx : Plancherel.SplitTorus.normalizedRealPart ha₁.isCentralSplitTorus.1.1 ωA ≠ 0 := by
    intro h0
    subst hωAdef
    exact (nonempty_unitaryCentralCharacter_of_normalizedRealPart_eq_zero l hl ha₁
      (hcpt k M hl.isConnectedReductive A₁ a₁ ha₁) ρ hirr ω hω hopen h0).elim hnu.false
  have hcent : ∀ ν : cocharacterLattice A₁,
      IsCentral (CommGroupScheme.groupHom ν ≫ a₁ ≫ l ≫ p) →
        pair A₁ (Plancherel.SplitTorus.normalizedRealPart ha₁.isCentralSplitTorus.1.1 ωA)
          ((1 : ℝ) ⊗ₜ[ℤ] ν) = 0 := by
    intro ν hν
    refine pair_normalizedRealPart_eq_zero_of_isCentral (q₁ ≫ (G.innerIso (z₁ i₁)).hom)
      (ψ₁.symm.hom ≫ lQ₁) rQ₁ hq₁' hlQ₁' hrQ₁ hmulQ₁' ha₁ π₁
      (unitaryCentralCharacterOfInjective cπ f hses.1) ωA hE₁ ν ?_
    rwa [hc₁']
  -- The cone complement statement identifies the two conjugated parabolics.
  obtain ⟨-, hrad⟩ := hcone k G hG P M A₁ p l a₁ hp hl hpG hmax ha₁ _ hx hcent Q₁ U₁ Q₂ U₂
    (q₁ ≫ (G.innerIso (z₁ i₁)).hom) (ψ₁.symm.hom ≫ lQ₁) rQ₁
    (q₂ ≫ (G.innerIso (z₂ i₂)).hom) (ψ₂.symm.hom ≫ lQ₂) rQ₂ hrQ₁ hrQ₂ hc₁' hc₂'
    (pres₁.conjugate (z₁ i₁) ψ₁ e₁ ha₁ he₁) (pres₂.conjugate (z₂ i₂) ψ₂ e₂ ha₁ he₂) hn₁' hn₂'
  have hE₂' : IsNormalizedJacquetExponent (q₁ ≫ (G.innerIso (z₁ i₁)).hom) (ψ₁.symm.hom ≫ lQ₁)
      rQ₁ hq₁' hlQ₁' hrQ₁ hmulQ₁' ha₁ π₂ ωA :=
    (isNormalizedJacquetExponent_congr (q₂ ≫ (G.innerIso (z₂ i₂)).hom) (ψ₂.symm.hom ≫ lQ₂) rQ₂
      hq₂' hlQ₂' hrQ₂ hmulQ₂' (q₁ ≫ (G.innerIso (z₁ i₁)).hom) (ψ₁.symm.hom ≫ lQ₁) rQ₁ hq₁'
      hlQ₁' hrQ₁ hmulQ₁' (hc₂'.trans hc₁'.symm) hrad.symm ha₁ π₂ ωA).mp hE₂
  -- Conjugations fixing `ωA` lie in the common parabolic.
  have hmem : ∀ (w : rationalPoints G) (ψ : M ≅ M) (e : A₁ ≅ A₁),
      ψ.hom ≫ l ≫ p = l ≫ p ≫ (G.innerIso w).hom →
      CommGroupScheme.groupHom e.hom ≫ a₁ = a₁ ≫ ψ.hom →
      ωA.comp (rationalPoints.map (CommGroupScheme.groupHom e.hom)) = ωA →
        w ∈ pointImage (q₁ ≫ (G.innerIso (z₁ i₁)).hom) := by
    intro w ψ e hψ he hωe
    have := ha₁.isAffine
    refine mem_pointImage_of_fixes hcone hnorm hG hp hl hpG hmax ha₁ hq₁' hrQ₁ hc₁'
      (pres₁.conjugate (z₁ i₁) ψ₁ e₁ ha₁ he₁) w ψ e hψ he _ hx hcent ?_
    rw [← Plancherel.SplitTorus.normalizedRealPart_comp_points ha₁.isCentralSplitTorus.1.1
      ha₁.isCentralSplitTorus.1.1 e.hom ωA hopen, hωe]
  -- Two distinct pieces along the common parabolic would carry `ωA`.
  obtain ⟨m, cc, z, hz, D, hglue⟩ := hgeo k G hG P M N Q₁ M U₁ p l r hp hl hr hmul
    (q₁ ≫ (G.innerIso (z₁ i₁)).hom) (ψ₁.symm.hom ≫ lQ₁) rQ₁ hq₁' hlQ₁' hrQ₁ hmulQ₁'
  have hex := (leviParabolicFunctorsExact.{u, max u v} k G hG Q₁ M U₁
    (q₁ ≫ (G.innerIso (z₁ i₁)).hom) (ψ₁.symm.hom ≫ lQ₁) rQ₁ hq₁' hlQ₁' hrQ₁ hmulQ₁').2 f g hses
  exact false_of_isNormalizedJacquetExponent_of_isShortExact D hglue cc hz hc₁' ρ hirr hsuper
    ha₁ ωA hωA hmem f g hex hE₁ hE₂'

end Langlands.Aubert.General.RepresentedParabolic
