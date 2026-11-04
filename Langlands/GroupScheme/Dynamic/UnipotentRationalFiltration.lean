import Langlands.GroupScheme.Dynamic.UnipotentGradedLie

/-! # The rational cyclic weight filtration of a dynamic unipotent subgroup -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry MvPolynomial
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.GroupScheme.Dynamic.GradedCoordinates

open Corepresented RelativeRoot

section General

/-- A homomorphism from a topological group to an additive group with a continuous section is an
open map. -/
theorem isOpenMap_of_continuous_section {H V : Type*} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [AddGroup V] [TopologicalSpace V] (q : H → V)
    (hq : ∀ a b, q (a * b) = q a + q b) (s : V → H) (hs : Continuous s)
    (hqs : ∀ v, q (s v) = v) : IsOpenMap q := by
  have hq1 : q 1 = 0 := by
    have h := hq 1 1
    rw [mul_one] at h
    exact left_eq_add.mp h
  have hqinv : ∀ a, q a⁻¹ = -q a := fun a => by
    have h := hq a⁻¹ a
    rw [inv_mul_cancel, hq1] at h
    exact eq_neg_of_add_eq_zero_left h.symm
  intro W hW
  have hset : q '' W = s ⁻¹' (W * {a | q a = 0}) := by
    ext v
    constructor
    · rintro ⟨a, ha, rfl⟩
      refine ⟨a, ha, a⁻¹ * s (q a), ?_, by group⟩
      change q (a⁻¹ * s (q a)) = 0
      rw [hq, hqinv, hqs, neg_add_cancel]
    · rintro ⟨a, ha, b, hb, hab⟩
      refine ⟨a, ha, ?_⟩
      have h := congrArg q hab
      rw [hq, show q b = 0 from hb, add_zero, hqs] at h
      exact h
  rw [hset]
  exact hW.mul_right.preimage hs

end General

section Filtration

variable {k : Type u} [Field k] (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffine G.X.left]
  [Smooth G.X.hom] [IsAffineHom G.X.hom] (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)

/-- The rational points of the cyclic weight filtration, shifted so that step `0` is the group
of rational points of the dynamic unipotent subgroup. -/
def rationalFiltration (r : ℕ) : Subgroup (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) :=
  (weightFiltration (S := Gm (Spec (CommRingCat.of k))) (AutomorphicAction.conjugation χ)
    (𝟙 _) (r + 1)).carrier (Over.mk (𝟙 _))

omit [IsAffine G.X.left] in
theorem rationalFiltration_zero :
    rationalFiltration G χ 0 = (Dynamic.unipotent χ).carrier (Over.mk (𝟙 _)) := by
  rw [rationalFiltration, dynamicUnipotent_eq_weightFiltration G χ]

omit [IsAffine G.X.left] [Smooth G.X.hom] in
theorem rationalFiltration_succ_le (r : ℕ) :
    rationalFiltration G χ (r + 1) ≤ rationalFiltration G χ r :=
  SubgroupFunctor.le_def.1 (weightFiltration_antitone _ _ (Nat.le_succ (r + 1))) _

omit [IsAffine G.X.left] [Smooth G.X.hom] in
theorem rationalFiltration_le_zero (r : ℕ) :
    rationalFiltration G χ r ≤ rationalFiltration G χ 0 :=
  SubgroupFunctor.le_def.1 (weightFiltration_antitone _ _ (by omega : 0 + 1 ≤ r + 1)) _

/-- The inverse of the structure map of the base test. -/
def fromBase (k : Type u) [Field k] :
    Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ (algSpec (CommRingCat.of k)).obj (op (baseTest k)) :=
  (Langlands.AlgebraicGeometry.PointTopology.ringTestSelfIso k).inv

theorem fromBase_toBase : fromBase k ≫ toBase (baseTest k) = 𝟙 _ :=
  (Over.mkIdTerminal (X := Spec (CommRingCat.of k))).hom_ext _ _

/-- Membership in the rational filtration, read in the model. -/
theorem mem_rationalFiltration_iff (r : ℕ) (p : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) :
    p ∈ rationalFiltration G χ r ↔
      modelPoint G (baseTest k) (toBase (baseTest k) ≫ p) ∈
        weightSubgroup (AffineCoordinates.corepresentation G) (cocharModelAction G χ)
          (Corepresented.cyclicTail (idExponent (k := k)) (r + 1)) (baseTest k) := by
  rw [← mem_weightFiltration_iff_modelPoint G χ (r + 1)]
  constructor
  · intro h
    exact SubgroupFunctor.comp_mem _ (toBase (baseTest k)) h
  · intro h
    have h' := SubgroupFunctor.comp_mem _ (fromBase k) h
    rwa [← Category.assoc, fromBase_toBase, Category.id_comp] at h'

/-- The cut point of a rational point of the dynamic unipotent subgroup. -/
def rationalCut (p : rationalFiltration G χ 0) : (unipotentCut G χ).obj (baseTest k) :=
  ⟨modelPoint G (baseTest k) (toBase (baseTest k) ≫ p.1),
    (mem_rationalFiltration_iff G χ 0 p.1).1 p.2⟩

theorem rationalCut_mul (p p' : rationalFiltration G χ 0) :
    rationalCut G χ (p * p') = rationalCut G χ p * rationalCut G χ p' := by
  apply Subtype.ext
  change modelPoint G (baseTest k) (toBase (baseTest k) ≫ (p.1 * p'.1)) =
    modelPoint G (baseTest k) (toBase (baseTest k) ≫ p.1) *
      modelPoint G (baseTest k) (toBase (baseTest k) ≫ p'.1)
  rw [MonObj.comp_mul, map_mul]

omit [IsAffine G.X.left] [Smooth G.X.hom] [IsAffineHom G.X.hom] in
theorem toBase_comp_mul (g p : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) :
    toBase (baseTest k) ≫ (g * p * g⁻¹) =
      (toBase (baseTest k) ≫ g) * (toBase (baseTest k) ≫ p) * (toBase (baseTest k) ≫ g)⁻¹ := by
  rw [MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv]

/-- Conjugation by a rational point commuting with `χ` preserves the rational filtration. -/
theorem conj_mem_rationalFiltration {r : ℕ} {g p : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X}
    (hg : g ∈ (torusCentralizer χ).carrier _) (hp : p ∈ rationalFiltration G χ r) :
    g * p * g⁻¹ ∈ rationalFiltration G χ r := by
  rw [mem_rationalFiltration_iff] at hp ⊢
  rw [toBase_comp_mul, map_mul, map_mul, map_inv]
  exact conj_mem_weightSubgroup_of_hat_eq _ _ _
    (hat_eq_of_fixed _ (constantFamily_naturality G g) (constantFamily_fixed G _ χ hg) _) hp

/-- A rational point commuting with `χ` normalizes every step of the rational filtration. -/
theorem mem_normalizer_rationalFiltration {g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X}
    (hg : g ∈ (torusCentralizer χ).carrier _) (r : ℕ) :
    g ∈ Subgroup.normalizer (rationalFiltration G χ r : Set _) := by
  rw [Subgroup.mem_normalizer_iff]
  intro p
  constructor
  · exact conj_mem_rationalFiltration G χ hg
  · intro h
    have hg' : g⁻¹ ∈ (torusCentralizer χ).carrier _ := ((torusCentralizer χ).carrier _).inv_mem hg
    have := conj_mem_rationalFiltration G χ hg' h
    rwa [inv_inv, show g⁻¹ * (g * p * g⁻¹) * g = p by group] at this

end Filtration

section Coordinates

variable {k : Type u} [Field k] (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffine G.X.left]
  [Smooth G.X.hom] [IsAffineHom G.X.hom] (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
  {n : ℕ} {d : Fin n → ℕ}
  {x : Fin n → AffineCoordinates.algebra G ⧸ weightIdeal (AffineCoordinates.corepresentation G)
    (cocharModelAction G χ) (Corepresented.cyclicTail (idExponent (k := k)) 1)}
  (hd : ∀ i, 0 < d i)
  (hx : ∀ i, IsHomogeneous (weightCorep (AffineCoordinates.corepresentation G)
      (cocharModelAction G χ) (Corepresented.cyclicTail (idExponent (k := k)) 1))
    (weightAction (AffineCoordinates.corepresentation G) (cocharModelAction G χ)
      (Corepresented.cyclicTail (idExponent (k := k)) 1)) (d i • idExponent (k := k)) (x i))
  (hbij : Function.Bijective (aeval x : MvPolynomial (Fin n) k →ₐ[k]
    AffineCoordinates.algebra G ⧸ weightIdeal (AffineCoordinates.corepresentation G)
      (cocharModelAction G χ) (Corepresented.cyclicTail (idExponent (k := k)) 1)))

variable (x) in
/-- The graded coordinates of a rational point of the dynamic unipotent subgroup. -/
def ratCoord (p : rationalFiltration G χ 0) (i : Fin n) : k :=
  coord (unipotentCorep G χ) (rationalCut G χ p) (x i)

include hx in
theorem ratCoord_mul {r : ℕ} (p p' : rationalFiltration G χ 0)
    (hp : p.1 ∈ rationalFiltration G χ r) (hp' : p'.1 ∈ rationalFiltration G χ r) {i : Fin n}
    (hi : d i = r + 1) :
    ratCoord G χ x (p * p') i = ratCoord G χ x p i + ratCoord G χ x p' i := by
  have hu : (rationalCut G χ p).1 ∈ weightSubgroup (AffineCoordinates.corepresentation G)
      (cocharModelAction G χ) (Corepresented.cyclicTail (idExponent (k := k)) (r + 1))
        (baseTest k) := (mem_rationalFiltration_iff G χ r p.1).1 hp
  have hu' : (rationalCut G χ p').1 ∈ weightSubgroup (AffineCoordinates.corepresentation G)
      (cocharModelAction G χ) (Corepresented.cyclicTail (idExponent (k := k)) (r + 1))
        (baseTest k) := (mem_rationalFiltration_iff G χ r p'.1).1 hp'
  unfold ratCoord
  rw [rationalCut_mul]
  exact coord_mul_of_weight_eq (AffineCoordinates.corepresentation G) (cocharModelAction G χ)
    idExponent_ne_zero hx (Nat.succ_pos r) (A := baseTest k) hu hu' hi

include hd hx hbij in
theorem mem_rationalFiltration_iff_ratCoord {r : ℕ} (p : rationalFiltration G χ 0) :
    p.1 ∈ rationalFiltration G χ r ↔ ∀ i, d i < r + 1 → ratCoord G χ x p i = 0 := by
  rw [mem_rationalFiltration_iff]
  exact mem_weightSubgroup_iff_coord_eq_zero _ _ idExponent_ne_zero hd hx hbij.2 (rationalCut G χ p)

include hd hx hbij in
/-- Conjugation by a rational point commuting with `χ` acts on the coordinates of weight `r + 1`
of points of the `r`-th step by the corresponding block of its linear part. -/
theorem ratCoord_conj {g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X}
    (hg : g ∈ (torusCentralizer χ).carrier _) {r : ℕ} (p : rationalFiltration G χ 0)
    (hp : p.1 ∈ rationalFiltration G χ r) {i : Fin n} (hi : d i = r + 1) :
    ratCoord G χ x ⟨g * p.1 * g⁻¹, conj_mem_rationalFiltration G χ hg p.2⟩ i =
      ∑ j ∈ Finset.univ.filter (fun j => d j = r + 1),
        conjMatrix (AffineCoordinates.corepresentation G) (cocharModelAction G χ)
          (constantFamily_naturality G g) (constantFamily_fixed G _ χ hg) idExponent_ne_zero hx
            hbij.2 i j * ratCoord G χ x p j := by
  have hcut : rationalCut G χ ⟨g * p.1 * g⁻¹, conj_mem_rationalFiltration G χ hg p.2⟩ =
      cutConj (AffineCoordinates.corepresentation G) (cocharModelAction G χ)
        (constantFamily_naturality G g) (constantFamily_fixed G _ χ hg) _ (baseTest k)
        (rationalCut G χ p) := by
    apply Subtype.ext
    change modelPoint G (baseTest k) (toBase (baseTest k) ≫ (g * p.1 * g⁻¹)) =
      constantFamily G g (baseTest k) * modelPoint G (baseTest k) (toBase (baseTest k) ≫ p.1) *
        (constantFamily G g (baseTest k))⁻¹
    rw [toBase_comp_mul, map_mul, map_mul, map_inv]
    rfl
  have hu : (rationalCut G χ p).1 ∈ weightSubgroup (AffineCoordinates.corepresentation G)
      (cocharModelAction G χ) (Corepresented.cyclicTail (idExponent (k := k)) (r + 1))
        (baseTest k) := (mem_rationalFiltration_iff G χ r p.1).1 hp
  unfold ratCoord
  rw [hcut, coord_cutConj_eq_sum (AffineCoordinates.corepresentation G) (cocharModelAction G χ)
    (constantFamily_naturality G g) (constantFamily_fixed G _ χ hg) idExponent_ne_zero hd hx
    hbij.2 (rationalCut G χ p) (Nat.succ_pos r) hu hi]
  rfl

include hd hx hbij in
/-- Beyond the largest weight, the rational filtration is trivial. -/
theorem rationalFiltration_eq_bot {N : ℕ} (hN : ∀ i, d i ≤ N) :
    rationalFiltration G χ N = ⊥ := by
  rw [eq_bot_iff]
  intro p hp
  have hp0 : p ∈ rationalFiltration G χ 0 := rationalFiltration_le_zero G χ N hp
  have hu : (rationalCut G χ ⟨p, hp0⟩).1 ∈ weightSubgroup (AffineCoordinates.corepresentation G)
      (cocharModelAction G χ) (Corepresented.cyclicTail (idExponent (k := k)) (N + 1))
        (baseTest k) := (mem_rationalFiltration_iff G χ N p).1 hp
  have h1 := eq_one_of_mem_weightSubgroup_of_lt (AffineCoordinates.corepresentation G)
    (cocharModelAction G χ) idExponent_ne_zero hd hx hbij.2 (fun i => Nat.lt_succ_of_le (hN i)) hu
  have h2 : modelPoint G (baseTest k) (toBase (baseTest k) ≫ p) = 1 := congrArg Subtype.val h1
  have h3 : toBase (baseTest k) ≫ p = toBase (baseTest k) ≫ 1 := by
    rw [MonObj.comp_one]
    apply modelPoint_injective G (baseTest k)
    rw [h2, map_one]
  have h4 := congrArg (fromBase k ≫ ·) h3
  simp only [← Category.assoc, fromBase_toBase, Category.id_comp] at h4
  exact (Subgroup.mem_bot).2 h4

variable (x) in
/-- The point of the first cyclic weight subgroup with prescribed graded coordinates. -/
def coordPoint (v : Fin n → k) : (unipotentCut G χ).obj (baseTest k) :=
  ofCoord (unipotentCorep G χ) ((aeval v).comp (AlgEquiv.ofBijective (aeval x) hbij).symm.toAlgHom)

omit [Smooth G.X.hom] [IsAffineHom G.X.hom] in
theorem coord_coordPoint (v : Fin n → k) (i : Fin n) :
    coord (unipotentCorep G χ) (coordPoint G χ x hbij v) (x i) = v i := by
  rw [coordPoint, coord_ofCoord, AlgHom.comp_apply]
  have : (AlgEquiv.ofBijective (aeval x) hbij).symm (x i) = X i := by
    apply (AlgEquiv.ofBijective (aeval x) hbij).injective
    rw [AlgEquiv.apply_symm_apply]
    exact (aeval_X x i).symm
  change aeval v ((AlgEquiv.ofBijective (aeval x) hbij).symm (x i)) = v i
  rw [this, aeval_X]

omit [Smooth G.X.hom] [IsAffineHom G.X.hom] in
theorem coord_coordPoint_val (v : Fin n → k) (b : AffineCoordinates.algebra G) :
    coord (AffineCoordinates.corepresentation G) (coordPoint G χ x hbij v).1 b =
      aeval v ((AlgEquiv.ofBijective (aeval x) hbij).symm (Ideal.Quotient.mk _ b)) := by
  rw [← coord_cut_mk, coordPoint, coord_ofCoord]
  rfl

section Topology

variable [TopologicalSpace k] [IsTopologicalRing k]

omit [Smooth G.X.hom] [IsAffineHom G.X.hom] [IsTopologicalRing k] in
theorem continuous_toBase_comp :
    letI := Langlands.AlgebraicGeometry.PointTopology.rationalPointTopology k G.X
    letI := G.affinePointsTopologicalSpace (baseTest k)
    Continuous fun p : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X => toBase (baseTest k) ≫ p := by
  let _ := Langlands.AlgebraicGeometry.PointTopology.rationalPointTopology k G.X
  let _ := G.affinePointsTopologicalSpace (baseTest k)
  have h : (fun p : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X => toBase (baseTest k) ≫ p) =
      fun p => rationalPointsAffineHomeomorph G p :=
    funext fun p => (rationalPointEquiv_eq_toBase p).symm
  rw [h]
  exact (rationalPointsAffineHomeomorph G).continuous

omit [IsTopologicalRing k] in
/-- The graded coordinates are continuous on the rational points. -/
theorem continuous_ratCoord (i : Fin n) :
    letI := Langlands.AlgebraicGeometry.PointTopology.rationalPointTopology k G.X
    Continuous fun p : rationalFiltration G χ 0 => ratCoord G χ x p i := by
  let _ := Langlands.AlgebraicGeometry.PointTopology.rationalPointTopology k G.X
  let _ := G.affinePointsTopologicalSpace (baseTest k)
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (x i)
  have h : (fun p : rationalFiltration G χ 0 => ratCoord G χ x p i) = fun p =>
      coord (AffineCoordinates.corepresentation G)
        (modelPoint G (baseTest k) (toBase (baseTest k) ≫ p.1)) b := by
    funext p
    unfold ratCoord
    rw [← hb]
    rfl
  rw [h]
  exact (continuous_coord_modelPoint G (baseTest k) b).comp
    ((continuous_toBase_comp G).comp continuous_subtype_val)

variable (x) in
/-- The rational point with prescribed graded coordinates. -/
def ratPoint (v : Fin n → k) : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X :=
  (Langlands.AlgebraicGeometry.PointTopology.rationalPointEquiv k G.X).symm
    ((modelPointEquiv G (baseTest k)).symm (coordPoint G χ x hbij v).1)

omit [Smooth G.X.hom] [IsAffineHom G.X.hom] [TopologicalSpace k] [IsTopologicalRing k] in
theorem modelPoint_toBase_ratPoint (v : Fin n → k) :
    modelPoint G (baseTest k) (toBase (baseTest k) ≫ ratPoint G χ x hbij v) =
      (coordPoint G χ x hbij v).1 := by
  rw [← rationalPointEquiv_eq_toBase]
  have h : Langlands.AlgebraicGeometry.PointTopology.rationalPointEquiv k G.X
      (ratPoint G χ x hbij v) = (modelPointEquiv G (baseTest k)).symm (coordPoint G χ x hbij v).1 :=
    Equiv.apply_symm_apply _ _
  rw [h, modelPoint_modelPointEquiv_symm]

omit [TopologicalSpace k] [IsTopologicalRing k] in
theorem ratPoint_mem (v : Fin n → k) : ratPoint G χ x hbij v ∈ rationalFiltration G χ 0 := by
  rw [mem_rationalFiltration_iff, modelPoint_toBase_ratPoint]
  exact (coordPoint G χ x hbij v).2

omit [TopologicalSpace k] [IsTopologicalRing k] in
theorem ratCoord_ratPoint (v : Fin n → k) (i : Fin n) :
    ratCoord G χ x ⟨ratPoint G χ x hbij v, ratPoint_mem G χ hbij v⟩ i = v i := by
  unfold ratCoord
  have : rationalCut G χ ⟨ratPoint G χ x hbij v, ratPoint_mem G χ hbij v⟩ =
      coordPoint G χ x hbij v := Subtype.ext (modelPoint_toBase_ratPoint G χ hbij v)
  rw [this, coord_coordPoint]

omit [Smooth G.X.hom] [IsAffineHom G.X.hom] in
/-- Rational points depend continuously on prescribed graded coordinates. -/
theorem continuous_ratPoint :
    letI := Langlands.AlgebraicGeometry.PointTopology.rationalPointTopology k G.X
    Continuous fun v : Fin n → k => ratPoint G χ x hbij v := by
  let _ := Langlands.AlgebraicGeometry.PointTopology.rationalPointTopology k G.X
  let _ := G.affinePointsTopologicalSpace (baseTest k)
  refine (rationalPointsAffineHomeomorph G).symm.continuous.comp
    (f := fun v => (modelPointEquiv G (baseTest k)).symm (coordPoint G χ x hbij v).1) ?_
  refine continuous_modelPointEquiv_symm G (baseTest k) fun b => ?_
  have h : (fun v : Fin n → k => coord (AffineCoordinates.corepresentation G)
      (coordPoint G χ x hbij v).1 b) = fun v =>
        eval v ((AlgEquiv.ofBijective (aeval x) hbij).symm (Ideal.Quotient.mk _ b)) := by
    funext v
    rw [coord_coordPoint_val]
    rfl
  rw [h]
  exact MvPolynomial.continuous_eval _

end Topology

end Coordinates

end Langlands.GroupScheme.Dynamic.GradedCoordinates
