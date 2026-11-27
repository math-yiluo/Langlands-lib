import Langlands.Shimura.PEL.HarrisProjectiveEndomorphismGraphPieces
import Langlands.AbelianScheme.RelativeHomNeronExtension
import Langlands.AlgebraicGeometry.Picard.LineHom.AffineExtension
import Langlands.Algebra.RationalPolynomialDilationProof

/-! # Finite endomorphism pieces for the same graph polynomial -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory Opposite Filter
open Langlands.AbelianScheme Langlands.GroupScheme.Cartier
open Langlands.AlgebraicGeometry.AlgebraicSpace Langlands.AlgebraicGeometry

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false

namespace Langlands.Shimura.PEL.ProjectiveEndomorphismGraphPieces

private theorem isIso_of_affine_hom_bijective {S₀ : Scheme.{u}} {Tgt : Over S₀} (f : Tgt ⟶ Tgt)
    (hf : ∀ T : Over S₀, IsAffine T.left → Function.Bijective (fun a : T ⟶ Tgt => a ≫ f)) :
    IsIso f := by
  let : IsIso ((schemeYoneda S₀).map f) :=
    Picard.LineHom.isIso_of_bijective_affine ((schemeSheaf S₀).obj Tgt).property
      ((schemeSheaf S₀).obj Tgt).property ((schemeYoneda S₀).map f)
      (fun T hT => Equiv.ulift.symm.bijective.comp ((hf T hT).comp Equiv.ulift.bijective))
  exact isIso_of_reflects_iso f (schemeYoneda S₀)

private theorem comparison_restrict {S₀ : Scheme.{u}} {A₀ B₀ : CommGroupScheme S₀}
    {Tgt : Over S₀}
    (β : (relativeHomFunctor A₀ B₀ ⋙ forget AddCommGrpCat.{u}) ≅ yoneda.obj Tgt)
    {T T' : Over S₀} (a : T' ⟶ T) (v : RelativeHom A₀ B₀ T) :
    β.hom.app (op T') (restrict A₀ B₀ a v) = a ≫ β.hom.app (op T) v := by
  have h := β.hom.naturality_apply a.op v
  simp only [Functor.comp_map] at h
  exact h

private theorem exists_extendingComparison {S₀ : Scheme.{u}} {A₀ B₀ : CommGroupScheme S₀}
    {Tgt : Over S₀} (α : (affineOverι S₀).op ⋙
      (relativeHomFunctor A₀ B₀ ⋙ forget AddCommGrpCat.{u}) ≅
      (affineOverι S₀).op ⋙ yoneda.obj Tgt) :
    ∃ β : (relativeHomFunctor A₀ B₀ ⋙ forget AddCommGrpCat.{u}) ≅ yoneda.obj Tgt,
      ∀ (T : Over S₀) [IsAffine T.left] (χ : RelativeHom A₀ B₀ T),
        β.hom.app (op T) χ = affHom α T χ := by
  obtain ⟨β⟩ := nonempty_iso_yoneda_of_affine α
  obtain ⟨v, hv⟩ := exists_universal_relativeHom α
  let e : Tgt ⟶ Tgt := β.hom.app (op Tgt) v
  have hmap (T : Over S₀) (a : T ⟶ Tgt) :
      β.hom.app (op T) (restrict A₀ B₀ a v) = a ≫ e :=
    comparison_restrict β a v
  have he_affine (T : Over S₀) [IsAffine T.left] :
      Function.Bijective (fun a : T ⟶ Tgt => a ≫ e) := by
    let a₁ : (T ⟶ Tgt) ≃ RelativeHom A₀ B₀ T :=
      (α.app (op ⟨T, inferInstance⟩)).symm.toEquiv
    let a₂ : RelativeHom A₀ B₀ T ≃ (T ⟶ Tgt) := (β.app (op T)).toEquiv
    have h : (fun a : T ⟶ Tgt => a ≫ e) = a₁.trans a₂ := by
      funext a
      change a ≫ e = β.hom.app (op T) (affInv α T a)
      exact (hmap T a).symm.trans (congrArg (β.hom.app (op T)) (hv T a))
    rw [h]
    exact (a₁.trans a₂).bijective
  let : IsIso e := isIso_of_affine_hom_bijective e fun T hT => by
    let := hT
    exact he_affine T
  refine ⟨β ≪≫ (yoneda.mapIso (asIso e)).symm, ?_⟩
  intro T _ χ
  let a := affHom α T χ
  have ha : restrict A₀ B₀ a v = χ := (hv T a).trans (affInv_affHom α T χ)
  change β.hom.app (op T) χ ≫ inv e = a
  calc
    β.hom.app (op T) χ ≫ inv e = (a ≫ e) ≫ inv e :=
      congrArg (fun k : T ⟶ Tgt => k ≫ inv e)
        ((congrArg (β.hom.app (op T)) ha.symm).trans (hmap T a))
    _ = a := by simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id]

variable {R : Type u} [CommRing R] {B : AbelianScheme (Spec (.of R))}
  {L : B.X.left.Modules} (G : ProjectiveEndomorphismGraphPieces B L)

local notation "S" => Spec (CommRingCat.of R)
local notation "E" => G.scheme
local notation "endFunctor" =>
  relativeHomFunctor B.toCommGroupScheme B.toCommGroupScheme ⋙ forget AddCommGrpCat
local notation "EndAt" => RelativeHom B.toCommGroupScheme B.toCommGroupScheme

/-- The affine graph comparison extends to the actual relative endomorphism
functor on all schemes over the base. -/
def comparisonAllTests : endFunctor ≅ yoneda.obj E :=
  Classical.choose (exists_extendingComparison G.comparison)

/-- On an affine test the extended comparison is the original graph-labelled
comparison. -/
theorem comparisonAllTests_affine (T : Over S) [IsAffine T.left] (χ : EndAt T) :
    (G.comparisonAllTests.hom.app (op T)) χ = affHom G.comparison T χ :=
  Classical.choose_spec (exists_extendingComparison G.comparison) T χ

/-- Dimensions of sections of powers of the actual graph line bundle on
a geometric fibre of an affine test. -/
def fibreGraphSectionRank {R' : Type u} [CommRing R'] (s : Spec (.of R') ⟶ S)
    (χ : EndAt (Over.mk s)) (K : Type u) [Field K] (sk : R' →+* K) (n : ℕ) : ℕ :=
  Scheme.Modules.geomFibreH0Finrank (pullback.snd B.X.hom s)
    (Nat.rec (motive := fun _ => (pullback B.X.hom s).Modules)
      (𝟙_ (pullback B.X.hom s).Modules)
      (fun _ M => M ⊗ ((Scheme.Modules.pullback (pullback.fst B.X.hom s)).obj L ⊗
        (Scheme.Modules.pullback (fstMap χ)).obj L)) n) K sk

/-- At an algebraically closed field test, the graph piece is determined
by the eventual section dimensions over that same field. -/
theorem range_subset_open_iff_self (p : Polynomial ℚ) {K : Type u}
    [Field K] [IsAlgClosed K] (s : Spec (.of K) ⟶ S) (χ : EndAt (Over.mk s)) :
    Set.range (G.comparisonAllTests.hom.app (op (Over.mk s)) χ).left ⊆ G.opens p ↔
      ∀ᶠ n : ℕ in atTop,
        (fibreGraphSectionRank (L := L) s χ K (RingHom.id K) n : ℚ) = p.eval (n : ℚ) := by
  let T := Over.mk s
  let : IsAffine T.left := inferInstanceAs (IsAffine (Spec (.of K)))
  let f := G.comparisonAllTests.hom.app (op T) χ
  have eval_of_range (q : Polynomial ℚ) (hq : Set.range f.left ⊆ G.opens q) :
      ∀ᶠ n : ℕ in atTop,
        (fibreGraphSectionRank (L := L) s χ K (RingHom.id K) n : ℚ) = q.eval (n : ℚ) := by
    have hc : f = G.comparison.hom.app (op ⟨T, inferInstance⟩) χ :=
      G.comparisonAllTests_affine T χ
    have hr : Set.range (G.comparison.hom.app (op ⟨T, inferInstance⟩) χ).left ⊆ G.opens q :=
      hc ▸ hq
    obtain ⟨n₀, hn₀⟩ := (G.range_subset_iff q K s χ).mp hr K (RingHom.id K)
    exact (eventually_ge_atTop n₀).mono hn₀
  constructor
  · exact eval_of_range p
  · intro hp
    let y := IsLocalRing.closedPoint K
    have hy : f.left y ∈ ⨆ q, G.opens q := by
      rw [G.cover]
      trivial
    obtain ⟨q, hq⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
    have hRange : Set.range f.left ⊆ G.opens q := by
      rintro _ ⟨z, rfl⟩
      have hz : z = y := Subsingleton.elim (α := PrimeSpectrum K) z y
      exact hz.symm ▸ hq
    have he := eval_of_range q hRange
    have heq : p = q := by
      apply Langlands.Algebra.RationalPolynomial.eq_of_eventually_nat_eval_eq
      filter_upwards [hp, he] with n hn hn'
      exact hn.symm.trans hn'
    exact heq.symm ▸ hRange

variable [IsNoetherianRing R]

/-- Each labelled open is finite over the affine base. Its closedness keeps
the Néron extension of a homomorphism in the same polynomial piece. -/
theorem open_isFinite (p : Polynomial ℚ) : IsFinite ((G.opens p).ι ≫ (E).hom) := by
  let : IsSeparated (E).hom := G.separated
  let : LocallyOfFiniteType (E).hom := G.locallyOfFiniteType
  let : FormallyUnramified (E).hom := G.formallyUnramified
  let : QuasiCompact ((G.opens p).ι ≫ (E).hom) := G.quasiCompact p
  have hclosed : UniversallyClosed ((G.opens p).ι ≫ (E).hom) :=
    universallyClosed_of_forall_isDiscreteValuationRing_hasLift ((G.opens p).ι ≫ (E).hom)
      (fun sq hR => hasLift_of_iso_yoneda_of_isClosed B G.comparisonAllTests
        neronHomExtension (G.opens p) (G.closed p) sq hR)
  let : IsProper ((G.opens p).ι ≫ (E).hom) :=
    { toIsSeparated := inferInstance, toUniversallyClosed := hclosed,
      toLocallyOfFiniteType := inferInstance }
  have := locallyQuasiFinite_of_formallyUnramified (E).hom
  exact IsFinite.of_isProper_of_locallyQuasiFinite _

end Langlands.Shimura.PEL.ProjectiveEndomorphismGraphPieces
