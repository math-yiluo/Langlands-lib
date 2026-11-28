import Langlands.Shimura.PEL.HarrisProjectiveEndomorphismFinitePieces
import Langlands.Shimura.PEL.HarrisIntegralCMClosedActionLocus
import Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleChartFiniteProducts

/-! # Finite polynomial bounds for integral Harris actions -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Filter
open Langlands.AlgebraicGeometry.AlgebraicSpace.FiniteProductCharts
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false

namespace Langlands.Shimura.PEL.HarrisPolarizedWeilLevel.GraphBoundedCMAction

open NumberField _root_.Algebra Langlands.AbelianScheme
open Langlands.AbelianScheme.PolarizedFiniteLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.GroupScheme.Cartier

variable {E F A : Type}
    [Field E] [NumberField E] [IsTotallyReal E]
    [Field F] [NumberField F] [IsTotallyComplex F]
    [Algebra E F] [IsQuadraticExtension E F]
    [Ring A] [Algebra E A] [Algebra F A] [IsScalarTower E F A]
    [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ F A]
    {n : ℕ} (D : CentralSimpleUnitaryData E F A n)
    {L : Type} [Field L] [NumberField L] [IsCMField L]
    [IsQuadraticExtension ℚ L] [Algebra L F]
    {τ₀ : L →+* ℂ}
    (C : HarrisSignatureCharts D.toSecondKindInvolution n
      (harrisCMSection E (algebraMap L F) τ₀))
    (P : Prerequisites.{0})
    (R : Type) [CommRing R] [IsNoetherianRing R]
    (p : Spec (.of R) ⟶ Spec (.of F))
    (B : Langlands.AbelianScheme (Spec (.of R)))
    {M : B.X.left.Modules} (G : ProjectiveEndomorphismGraphPieces B M)
    (W : DualWitness B) (lam : B ⟶ W.dual P)

local notation "S" => Spec (CommRingCat.of R)
local notation "basisO" => D.harrisHodgePELIntegralBasis C
private abbrev orderIndices := Fin (Module.finrank ℤ (D.harrisHodgePELIntegralOrder C))
local notation "OrderIndices" => orderIndices D C
local notation "E₀" => G.scheme
local notation "tuple" => ∏ᶜ fun _ : OrderIndices => E₀
local notation "tupleπ" i:max => Pi.π (fun _ : OrderIndices => E₀) i

local instance : IsSeparated (E₀).hom := G.separated
local instance : LocallyOfFiniteType (E₀).hom := G.locallyOfFiniteType

local notation "eE" => Functor.isoWhiskerLeft (locallyNoetherianTestInclusion S).op
  G.comparisonAllTests
local notation "raw" => (relativeIntegralActionLocusTest E₀ B basisO eE).obj
local notation "Z" => harrisIntegralCMClosedActionLocus D C P p B W lam E₀ eE
local notation "inc" => harrisIntegralCMClosedActionLocusInclusion D C P p B W lam E₀ eE
local notation "rawInc" => relativeIntegralActionLocusInclusion B basisO E₀ eE
  (relativeEndomorphismPower_isLocallyNoetherian (I := OrderIndices) E₀)

/-- The actual closed inclusion of the joint action locus into the full
relative tuple of endomorphisms. -/
def actionTupleInclusion : Z ⟶ tuple := inc ≫ rawInc

local notation "c" => actionTupleInclusion D C P R p B G W lam

instance actionTupleInclusion_isClosedImmersion : IsClosedImmersion (c).left := by
  change IsClosedImmersion ((inc).left ≫ (rawInc).left)
  infer_instance

variable (polynomial : orderIndices D C → Polynomial ℚ)

local notation "piece" i:max => Over.mk ((G.opens (polynomial i)).ι ≫ (E₀).hom)
local notation "boundedTuple" => ∏ᶜ fun i : OrderIndices => piece i

private def boundedTupleInclusion : boundedTuple ⟶ tuple :=
  Pi.lift (fun i : OrderIndices => Pi.π (fun j : OrderIndices => piece j) i ≫
    Over.homMk (G.opens (polynomial i)).ι rfl)

local notation "j" => boundedTupleInclusion D C R B G polynomial

omit [IsScalarTower ℚ F A] in
private theorem boundedTuple_isFinite : IsFinite (boundedTuple).hom := by
  let : MorphismProperty.ContainsIdentities (@IsFinite : MorphismProperty Scheme.{0}) :=
    ⟨fun _ => inferInstance⟩
  let : MorphismProperty.RespectsIso (@IsFinite : MorphismProperty Scheme.{0}) :=
    MorphismProperty.respectsIso_of_isStableUnderComposition
      (fun _ _ f (_ : IsIso f) => inferInstance)
  exact overFiniteProduct_property (@IsFinite : MorphismProperty Scheme.{0})
    (fun i : OrderIndices => piece i) (fun i => G.open_isFinite (polynomial i))

/-- A tuple of specified graph polynomials cuts out an actual base change
of the joint integral action, determinant and Rosati locus. -/
def scheme : Over S :=
  Over.mk (pullback.snd (c).left (j).left ≫ (boundedTuple).hom)

local notation "W₀" => scheme D C P R p B G W lam polynomial

instance scheme_isFinite : IsFinite (W₀).hom := by
  let : IsFinite (boundedTuple).hom := boundedTuple_isFinite D C R B G polynomial
  have : IsClosedImmersion (pullback.snd (c).left (j).left) := inferInstance
  change IsFinite (pullback.snd (c).left (j).left ≫ (boundedTuple).hom)
  infer_instance

/-- Forget the polynomial bounds on the joint action. -/
def inclusion : W₀ ⟶ Z :=
  Over.homMk (pullback.fst (c).left (j).left) (by
    change pullback.fst (c).left (j).left ≫ (Z).hom =
      pullback.snd (c).left (j).left ≫ (boundedTuple).hom
    rw [← Over.w c, ← Category.assoc, pullback.condition, Category.assoc, Over.w j])

local notation "incl" => inclusion D C P R p B G W lam polynomial

omit [IsScalarTower ℚ F A] [IsNoetherianRing R] in
private theorem boundedTupleInclusion_proj (i : OrderIndices) :
    j ≫ tupleπ i = Pi.π (fun k : OrderIndices => piece k) i ≫
      Over.homMk (G.opens (polynomial i)).ι rfl := by
  simp [boundedTupleInclusion]

private instance boundedTupleInclusion_mono : Mono j := by
  constructor
  intro T f g h
  apply Pi.hom_ext
  intro i
  let k : piece i ⟶ E₀ := Over.homMk (G.opens (polynomial i)).ι rfl
  let : Mono k := Over.mono_of_mono_left k
  apply (cancel_mono k).mp
  have hi := congrArg (fun t : T ⟶ tuple => t ≫ tupleπ i) h
  simpa only [Category.assoc, boundedTupleInclusion_proj, k] using hi

instance inclusion_mono : Mono incl := by
  let : Mono (j).left := Over.mono_left_of_mono j
  let : Mono (incl).left := inferInstanceAs (Mono (pullback.fst (c).left (j).left))
  exact Over.mono_of_mono_left incl

local notation "Tests" => ObjectProperty.FullSubcategory
  (fun T : Over (Spec (CommRingCat.of R)) => IsLocallyNoetherian T.left)

/-- The classified integral action on the original test family. -/
def actionOf (T₀ : Tests) (f : T₀.obj ⟶ Z) :
    D.harrisHodgePELIntegralOrder C →+*
      CategoryTheory.End ((AbelianScheme.baseChange T₀.obj.hom).obj B) :=
  (harrisIntegralCMClosedActionLocusFullHomEquiv D C P p B W lam E₀ eE T₀ f).val

set_option maxHeartbeats 3500000 in
/-- Each polynomial coordinate classifies the actual image of the
corresponding integral order basis element. -/
theorem coordinate_classifies_basis (T₀ : Tests) (f : T₀.obj ⟶ Z) (i : OrderIndices) :
    G.comparisonAllTests.hom.app (op T₀.obj)
      ((actionOf D C P R p B G W lam T₀ f (basisO i)).asHom) =
      f ≫ c ≫ tupleπ i := by
  let H := relativeEndomorphismPower_isLocallyNoetherian (I := OrderIndices) E₀
  let u := relativeIntegralActionLocusHomEquiv B basisO E₀ eE H T₀ (f ≫ inc)
  change G.comparisonAllTests.hom.app (op T₀.obj) (u (basisO i)).asHom = _
  rw [relativeIntegralActionLocusHomEquiv_apply_basis]
  let v := ((f ≫ inc) ≫ rawInc) ≫ tupleπ i
  change G.comparisonAllTests.hom.app (op T₀.obj)
    (G.comparisonAllTests.inv.app (op T₀.obj) v) = _
  rw [G.comparisonAllTests.inv_hom_id_app_apply]
  simp only [v, actionTupleInclusion, Category.assoc]

/-- A map into the full joint action locus factors through the finite scheme
exactly when each of its coordinate maps lands in the indicated graph piece. -/
theorem factors_iff (T : Over S) (f : T ⟶ Z) :
    (∃ f' : T ⟶ W₀, f' ≫ incl = f) ↔
      ∀ i : OrderIndices, Set.range (f ≫ c ≫ tupleπ i).left ⊆ G.opens (polynomial i) := by
  constructor
  · rintro ⟨l, rfl⟩ i
    let q : W₀ ⟶ boundedTuple := Over.homMk (pullback.snd (c).left (j).left) rfl
    have h : incl ≫ c = q ≫ j := by
      apply Over.OverMorphism.ext
      exact pullback.condition
    have hp : (l ≫ incl) ≫ c ≫ tupleπ i =
        ((l ≫ q) ≫ Pi.π (fun k : OrderIndices => piece k) i) ≫
          Over.homMk (G.opens (polynomial i)).ι rfl := by
      rw [Category.assoc, ← Category.assoc (incl), h]
      simp only [Category.assoc, boundedTupleInclusion_proj]
    rw [hp]
    rintro _ ⟨x, rfl⟩
    simp only [Over.comp_left, Scheme.Hom.comp_apply]
    exact Subtype.property _
  · intro hf
    let r (i : OrderIndices) : T ⟶ piece i :=
      Over.homMk (IsOpenImmersion.lift (G.opens (polynomial i)).ι (f ≫ c ≫ tupleπ i).left (by
        intro y hy
        exact ⟨⟨y, hf i hy⟩, rfl⟩)) (by
          change _ ≫ ((G.opens (polynomial i)).ι ≫ (E₀).hom) = _
          rw [← Category.assoc, IsOpenImmersion.lift_fac]
          exact Over.w (f ≫ c ≫ tupleπ i))
    let q : T ⟶ boundedTuple := Pi.lift r
    have hq : q ≫ j = f ≫ c := by
      apply Pi.hom_ext
      intro i
      have hp : q ≫ Pi.π (fun k : OrderIndices => piece k) i = r i := by simp [q]
      rw [Category.assoc, boundedTupleInclusion_proj, ← Category.assoc, hp, Category.assoc]
      apply Over.OverMorphism.ext
      exact IsOpenImmersion.lift_fac _ _ _
    have he : f.left ≫ (c).left = q.left ≫ (j).left :=
      (congrArg Over.Hom.left hq).symm
    let l : T ⟶ W₀ := Over.homMk (pullback.lift f.left q.left he) (by
      change pullback.lift f.left q.left he ≫
        (pullback.snd (c).left (j).left ≫ (boundedTuple).hom) = T.hom
      rw [← Category.assoc, pullback.lift_snd]
      exact Over.w q)
    exact ⟨l, Over.OverMorphism.ext (pullback.lift_fst _ _ _)⟩

private def geometricTest {T : Over (Spec (CommRingCat.of R))}
    {K : Type} [Field K] (a : Spec (.of K) ⟶ T.left) : Tests :=
  ⟨Over.mk (a ≫ T.hom), inferInstanceAs (IsLocallyNoetherian (Spec (.of K)))⟩

private def geometricTestMap {T : Over (Spec (CommRingCat.of R))}
    {K : Type} [Field K] (a : Spec (.of K) ⟶ T.left) : (geometricTest R a).obj ⟶ T :=
  Over.homMk a rfl

set_option maxHeartbeats 4000000 in
/-- Computing the graph polynomials on the geometric points of an actual
classifying map gives its factorization through the finite action scheme. -/
theorem factors_of_geometric_graphPolynomials (T : Over S) (f : T ⟶ Z)
    (hpoly : ∀ (K : Type) [Field K] [IsAlgClosed K]
      (a : Spec (.of K) ⟶ T.left) (i : OrderIndices),
      let s := a ≫ T.hom
      let χ := ((actionOf D C P R p B G W lam (geometricTest R a)
        (geometricTestMap R a ≫ f)) (basisO i)).asHom
      ∀ᶠ k : ℕ in atTop,
        (ProjectiveEndomorphismGraphPieces.fibreGraphSectionRank (L := M)
          s χ K (RingHom.id K) k : ℚ) = (polynomial i).eval (k : ℚ)) :
    ∃ f' : T ⟶ W₀, f' ≫ incl = f := by
  apply (factors_iff D C P R p B G W lam polynomial T f).mpr
  intro i y hy
  obtain ⟨x, rfl⟩ := hy
  let K := AlgebraicClosure (T.left.residueField x)
  let b := Spec.map (CommRingCat.ofHom (algebraMap (T.left.residueField x) K))
  let a := b ≫ T.left.fromSpecResidueField x
  let z := IsLocalRing.closedPoint K
  have hz : a z = x := by
    change T.left.fromSpecResidueField x (b z) = x
    exact T.left.fromSpecResidueField_apply x (b z)
  let s := a ≫ T.hom
  let f' := geometricTestMap R a ≫ f
  let χ := ((actionOf D C P R p B G W lam (geometricTest R a) f') (basisO i)).asHom
  have hq := (G.range_subset_open_iff_self (polynomial i) s χ).mpr (hpoly K a i)
  have hh : G.comparisonAllTests.hom.app (op (geometricTest R a).obj) χ =
      f' ≫ c ≫ tupleπ i :=
    coordinate_classifies_basis D C P R p B G W lam (geometricTest R a) f' i
  have hmem : (f' ≫ c ≫ tupleπ i).left z ∈ G.opens (polynomial i) :=
    (hh ▸ hq) (Set.mem_range_self z)
  change ((geometricTestMap R a ≫ f) ≫ c ≫ tupleπ i).left z ∈ _ at hmem
  rw [Category.assoc] at hmem
  change (f ≫ c ≫ tupleπ i).left (a z) ∈ _ at hmem
  rw [hz] at hmem
  exact hmem

end Langlands.Shimura.PEL.HarrisPolarizedWeilLevel.GraphBoundedCMAction
