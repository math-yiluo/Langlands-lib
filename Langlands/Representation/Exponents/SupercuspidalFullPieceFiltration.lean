import Langlands.Representation.Exponents.ActualGeometricFullPiece
import Langlands.Representation.Exponents.LeviSupercuspidalInductionSupport
import Langlands.Representation.Geometric.FullIntersectionIrreducible
import Langlands.Representation.Filtration.GluedAtObject

/-! # Filtration by the full geometric pieces of a supercuspidal induction -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [TopologicalSpace k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance fullFiltrationAmbientTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {P M N Q L U : GroupScheme (Spec (CommRingCat.of k))}
  {p : P ⟶ G} {l : M ⟶ P} {r : N ⟶ P} {hp : IsParabolicSubgroup p}
  {hr : LeviSubgroup.IsGeometricUnipotentRadical r} {hl : IsRationalLeviSubgroup l}
  {hmul : IsIso (subgroupMultiplication l r)}
  {q : Q ⟶ G} {lQ : L ⟶ Q} {rQ : U ⟶ Q} {hq : IsParabolicSubgroup q}
  {hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ} {hlQ : IsRationalLeviSubgroup lQ}
  {hmulQ : IsIso (subgroupMultiplication lQ rQ)}

namespace GeometricLemmaIntersectionDatum

variable {z : rationalPoints G}
  (D : GeometricLemmaIntersectionDatum p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ z)

omit [T2Space k] [IsAffineHom G.X.hom]
  [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)] in
/-- Inverting the full-piece conjugacy gives the orientation used by the
conjugate of the original inducing representation. -/
theorem fullLeviConjugacy_inv [IsIso D.p'] [IsIso D.q'] :
    D.fullLeviConjugacy.val.inv ≫ l ≫ p = lQ ≫ q ≫ (G.innerIso z).hom := by
  have h := congrArg
    (fun f : M ⟶ G => D.fullLeviConjugacy.val.inv ≫ f ≫ (G.innerIso z).hom)
    D.fullLeviConjugacy.property
  simpa only [innerIso_inv_hom, Category.assoc, Iso.inv_hom_id_assoc,
    Iso.inv_hom_id, Category.comp_id] using h.symm

omit [T2Space k] [IsAffineHom G.X.hom]
  [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)] in
/-- The inverse full-piece point equivalence is the map of the inverse
scheme isomorphism. -/
@[simp] theorem fullLeviPointsEquiv_symm_apply [IsIso D.p'] [IsIso D.q']
    (x : rationalPoints L) :
    letI := leviPointTopology l hl
    letI := leviPointTopology lQ hlQ
    D.fullLeviPointsEquiv.symm x = rationalPoints.map D.fullLeviConjugacy.val.inv x := by
  let := leviPointTopology l hl
  let := leviPointTopology lQ hlQ
  apply D.fullLeviPointsEquiv.injective
  rw [D.fullLeviPointsEquiv.apply_symm_apply, D.fullLeviPointsEquiv_apply,
    ← pointMap_comp_apply, Iso.inv_hom_id]
  rfl

end GeometricLemmaIntersectionDatum

/-- Compose nonempty equivalences of representations. -/
theorem nonempty_representationEquiv_trans {A G V W X : Type*} [Semiring A] [Monoid G]
    [AddCommMonoid V] [AddCommMonoid W] [AddCommMonoid X] [Module A V] [Module A W]
    [Module A X] {ρ : Representation A G V} {σ : Representation A G W}
    {τ : Representation A G X} (h₁ : Nonempty (ρ.Equiv σ)) (h₂ : Nonempty (σ.Equiv τ)) :
    Nonempty (ρ.Equiv τ) :=
  ⟨h₁.some.trans h₂.some⟩

/-- An actual filtration retaining every full source-intersection piece of
a supplied geometric gluing. This does not identify the selected indices
with the conjugating double cosets. -/
structure FullPieceFiltrationData {n : ℕ} (z : Fin n → rationalPoints G)
    (D : ∀ i, GeometricLemmaIntersectionDatum p l r hp hr hl hmul
      q lQ rQ hq hrQ hlQ hmulQ (z i))
    (ρ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M)) where
  length : ℕ
  enumeration : Fin length ≃ {i : Fin n // IsIso (D i).p'}
  conjugacy : Fin length → (L ≅ M)
  points : letI := leviPointTopology l hl
    letI := leviPointTopology lQ hlQ
    Fin length → (rationalPoints L ≃ₜ* rationalPoints M)
  conjugacy_eq : ∀ i, (conjugacy i).hom ≫ l ≫ p =
    lQ ≫ q ≫ (G.innerIso (z (enumeration i).val)).hom
  points_apply : ∀ i x, points i x = rationalPoints.map (conjugacy i).hom x
  filtration : letI := leviPointTopology l hl
    ObjectRepFiltration
      ((leviJacquetInductionFunctor p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ).obj ρ)
      length
  graded : letI := leviPointTopology l hl
    letI := leviPointTopology lQ hlQ
    ∀ i, Nonempty ((filtration.gradedRepresentation i).ρ.Equiv
      (SmoothRep.pullback (points i) ρ).representation)

/-- Evaluate the supplied gluing on a supercuspidal representation, delete
its proper source-intersection factors and identify every retained grade
with the original representation along its actual Levi conjugacy. -/
theorem nonempty_fullPieceFiltrationData {n : ℕ} (z : Fin n → rationalPoints G)
    (D : ∀ i, GeometricLemmaIntersectionDatum p l r hp hr hl hmul
      q lQ rQ hq hrQ hlQ hmulQ (z i))
    (hglued : IsGluedFrom
      (leviJacquetInductionFunctor.{u, v} p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ)
      (fun i => (D i).pieceFunctor))
    (E : M ≅ L)
    (ρ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M))
    (hρ : haveI := hl.isConnectedReductive.isAffineHom
      letI := leviPointTopology l hl
      haveI := leviPoints_locallyCompactSpace p l hp hl
      haveI := leviPoints_nonarchimedeanGroup p l hp hl
      IsSupercuspidal ρ) : Nonempty (FullPieceFiltrationData z D ρ) := by
  classical
  have := hl.isConnectedReductive.isAffineHom
  have := hlQ.isConnectedReductive.isAffineHom
  let := leviPointTopology l hl
  let := leviPointTopology lQ hlQ
  have := leviPoints_locallyCompactSpace p l hp hl
  have := leviPoints_nonarchimedeanGroup p l hp hl
  have := leviPoints_locallyCompactSpace q lQ hq hlQ
  have := leviPoints_nonarchimedeanGroup q lQ hq hlQ
  have hzero (i : Fin n) (hi : ¬ IsIso (D i).p') :
      Subsingleton ((D i).pieceFunctor.obj ρ) :=
    (D i).subsingleton_pieceFunctor_obj ρ
      (hρ (D i).P' (D i).M' (D i).N' (D i).p' (D i).l' (D i).r'
        (D i).hp' (D i).hl' (D i).hr' (D i).hmul' hi)
  obtain ⟨m, c, s, hs⟩ :=
    hglued.exists_selected_filtration ρ (fun i => IsIso (D i).p') hzero
  have hp' (i : Fin m) : IsIso (D (c i).val).p' := (c i).property
  have hq' (i : Fin m) : IsIso (D (c i).val).q' := by
    let := hp' i
    exact (D (c i).val).isIso_q'_of_isIso_p'_of_iso E
  let φ : Fin m → (L ≅ M) := fun i =>
    let := hp' i
    let := hq' i
    (D (c i).val).fullLeviConjugacy.val.symm
  let e : Fin m → (rationalPoints L ≃ₜ* rationalPoints M) := fun i =>
    let := hp' i
    let := hq' i
    (D (c i).val).fullLeviPointsEquiv.symm
  refine ⟨⟨m, c, φ, e, ?_, ?_, s, ?_⟩⟩
  · intro i
    let := hp' i
    let := hq' i
    exact (D (c i).val).fullLeviConjugacy_inv
  · intro i x
    let := hp' i
    let := hq' i
    exact (D (c i).val).fullLeviPointsEquiv_symm_apply x
  · intro i
    let := hp' i
    let := hq' i
    exact nonempty_representationEquiv_trans (hs i) ⟨(D (c i).val).fullPieceEquiv ρ⟩

/-- A chosen filtration by the full geometric pieces of a supercuspidal
representation. -/
def fullPieceFiltration {n : ℕ} (z : Fin n → rationalPoints G)
    (D : ∀ i, GeometricLemmaIntersectionDatum p l r hp hr hl hmul
      q lQ rQ hq hrQ hlQ hmulQ (z i))
    (hglued : IsGluedFrom
      (leviJacquetInductionFunctor.{u, v} p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ)
      (fun i => (D i).pieceFunctor))
    (E : M ≅ L)
    (ρ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M))
    (hρ : haveI := hl.isConnectedReductive.isAffineHom
      letI := leviPointTopology l hl
      haveI := leviPoints_locallyCompactSpace p l hp hl
      haveI := leviPoints_nonarchimedeanGroup p l hp hl
      IsSupercuspidal ρ) : FullPieceFiltrationData z D ρ :=
  Classical.choice (nonempty_fullPieceFiltrationData z D hglued E ρ hρ)

end Langlands.Aubert.General.RepresentedParabolic
