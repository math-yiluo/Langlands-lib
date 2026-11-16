import Langlands.GroupScheme.Reductive.SplitBorelPositiveCoordinates
import Langlands.GroupScheme.Dynamic.AffineRepresentability

/-! # Ordered positive products and the actual contracting group -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.LocalSplitCell

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I] {J : Type u}
  {G : GroupScheme (Spec (CommRingCat.of R))}
  {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
  {ch : J → I → ℤ} {u : J → (Ga R ⟶ G)}

/-- Positive ordered products contract to one on every test scheme. -/
theorem orderedProduct_mem_unipotent
    (hu : TorusEquivariant i ch u) (ν : I → ℤ)
    {r : ℕ} (e : Fin r → J) (he : ∀ k, 0 < coPairing (ch (e k)) ν)
    (Z : Over (Spec (CommRingCat.of R))) (c : Fin r → Γ(Z.left, ⊤)) :
    orderedProduct u e Z c ∈ (Dynamic.unipotent (AffineRegularBorel.cocharacter i ν)).carrier Z := by
  classical
  have hd : ∀ k, ∃ d : ℕ, 0 < d ∧ coPairing (ch (e k)) ν = d := fun k =>
    ⟨(coPairing (ch (e k)) ν).toNat, by have := he k; omega,
      (Int.toNat_of_nonneg (he k).le).symm⟩
  choose d hd0 hdeq using hd
  let L := AffineLine.scheme (Spec (CommRingCat.of R))
  let t := AffineLine.homEquiv (Z ⊗ L) (snd Z L)
  let E := orderedProduct u e (Z ⊗ L)
    (fun k => t ^ d k * (fst Z L).left.appTop (c k))
  refine ⟨E, ?_, ?_⟩
  · let W := Z ⊗ (Gm (Spec (CommRingCat.of R))).X
    let a := snd Z (Gm (Spec (CommRingCat.of R))).X
    let v := Gm.pointsEquiv _ W a
    have ht : (Z ◁ AffineLine.unitInclusion _).left.appTop t = (v : Γ(W.left, ⊤)) := by
      dsimp only [t]
      rw [← AffineLine.homEquiv_comp]
      rw [whiskerLeft_snd, AffineLine.homEquiv_comp_unitInclusion]
    have hf (k : Fin r) : (Z ◁ AffineLine.unitInclusion _).left.appTop
        ((fst Z L).left.appTop (c k)) = (fst Z (Gm (Spec (CommRingCat.of R))).X).left.appTop (c k) := by
      rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, ← Over.comp_left,
        whiskerLeft_fst]
    have hχ : a ≫ (AffineRegularBorel.cocharacter i ν).hom.hom =
        cocharPoint ν W v ≫ i.hom.hom := by
      rw [cocharPoint_eq_comp, MulEquiv.symm_apply_apply, Category.assoc]
      rfl
    change (Z ◁ AffineLine.unitInclusion _) ≫ E = _
    rw [comp_orderedProduct]
    simp only [map_mul, map_pow, ht, hf]
    rw [Dynamic.orbit, hχ, comp_orderedProduct,
      torus_mul_orderedProduct_mul_inv hu]
    simp only [torusChar_cocharPoint_of_eq (hdeq _)]
    rfl
  · let z : Z ⟶ Z ⊗ L := lift (𝟙 Z) (toUnit Z ≫ AffineLine.zeroSection _)
    have ht : z.left.appTop t = 0 := by
      dsimp only [t, z]
      rw [← AffineLine.homEquiv_comp]
      rw [lift_snd, AffineLine.homEquiv_comp_zeroSection]
    change z ≫ E = _
    rw [comp_orderedProduct]
    simp only [map_mul, map_pow, ht, zero_pow (hd0 _).ne', zero_mul]
    exact orderedProduct_zero u e Z

/-- The ordered root product as an actual morphism from affine coordinate space. -/
def positiveProductMap (u : J → (Ga R ⟶ G)) {n : ℕ} (pos : Fin n → J) :
    (VectorGroup.groupScheme (CommRingCat.of R) n).X ⟶ G.X :=
  orderedProduct u pos _ ((VectorGroup.coordinates (CommRingCat.of R) n _ (𝟙 _)).toAdd)

/-- The positive product morphism has the expected formula on all tests. -/
theorem comp_positiveProductMap {n : ℕ} (pos : Fin n → J)
    {Z : Over (Spec (CommRingCat.of R))}
    (x : Z ⟶ (VectorGroup.groupScheme (CommRingCat.of R) n).X) :
    x ≫ positiveProductMap u pos =
      orderedProduct u pos Z ((VectorGroup.coordinates (CommRingCat.of R) n Z x).toAdd) := by
  rw [positiveProductMap, comp_orderedProduct]
  congr 1

/-- Positive product maps are monomorphisms whenever the big cell is an open immersion. -/
theorem positiveProductMap_mono {m n : ℕ} {neg : Fin m → J} {pos : Fin n → J}
    [IsOpenImmersion (cellMap i u neg pos).left] : Mono (positiveProductMap u pos) := by
  constructor
  intro Z f g h
  apply (VectorGroup.coordinates (CommRingCat.of R) n Z).injective
  apply Multiplicative.toAdd.injective
  apply orderedProduct_pos_injective (i := i) (u := u) (neg := neg) (pos := pos) Z
  rwa [← comp_positiveProductMap, ← comp_positiveProductMap]

/-- The affine-test coordinate theorem transports to every affine test scheme. -/
theorem exists_orderedProduct_eq_of_mem_unipotent_of_affine
    {m n : ℕ} {neg : Fin m → J} {pos : Fin n → J}
    [IsOpenImmersion (cellMap i u neg pos).left]
    (hu : TorusEquivariant i ch u) (ν : I → ℤ)
    (hneg : ∀ k, coPairing (ch (neg k)) ν < 0)
    {Z : Over (Spec (CommRingCat.of R))} [IsAffine Z.left]
    (g : Z ⟶ G.X)
    (hg : g ∈ (Dynamic.unipotent (AffineRegularBorel.cocharacter i ν)).carrier Z) :
    ∃ c : Fin n → Γ(Z.left, ⊤), g = orderedProduct u pos Z c := by
  let e : Over.mk (Z.left.isoSpec.inv ≫ Z.hom) ≅ Z :=
    Over.isoMk Z.left.isoSpec.symm rfl
  obtain ⟨c, hc⟩ := exists_orderedProduct_eq_of_mem_unipotent_of_ring (pos := pos)
    hu ν hneg _ (e.hom ≫ g)
      ((Dynamic.unipotent (AffineRegularBorel.cocharacter i ν)).comp_mem e.hom hg)
  refine ⟨fun k => e.inv.left.appTop (c k), ?_⟩
  have h := congrArg (fun f => e.inv ≫ f) hc
  rwa [← Category.assoc, e.inv_hom_id, Category.id_comp, comp_orderedProduct] at h

section Represented

variable {U : GroupScheme (Spec (CommRingCat.of R))} (j : U ⟶ G)
  (hu : TorusEquivariant i ch u) (ν : I → ℤ)
  (hU : (Dynamic.unipotent (AffineRegularBorel.cocharacter i ν)).IsRepresentedBy j)
  {m n : ℕ} {neg : Fin m → J} {pos : Fin n → J}

include hu hU in
/-- Positive products factor through the actual representative of the contracting group. -/
theorem exists_positiveProduct_lift (hpos : ∀ k, 0 < coPairing (ch (pos k)) ν) :
    ∃ f : (VectorGroup.groupScheme (CommRingCat.of R) n).X ⟶ U.X,
      f ≫ j.hom.hom = positiveProductMap u pos := by
  have h := orderedProduct_mem_unipotent hu ν pos hpos
    (VectorGroup.groupScheme (CommRingCat.of R) n).X
    ((VectorGroup.coordinates (CommRingCat.of R) n _ (𝟙 _)).toAdd)
  rw [← hU.2] at h
  exact SubgroupFunctor.mem_range.mp h

/-- The positive product morphism with target the actual contracting group. -/
def positiveProductToUnipotent (hpos : ∀ k, 0 < coPairing (ch (pos k)) ν) :
    (VectorGroup.groupScheme (CommRingCat.of R) n).X ⟶ U.X :=
  (exists_positiveProduct_lift j hu ν hU hpos).choose

/-- Composing the lifted positive product with the subgroup inclusion recovers the product. -/
theorem positiveProductToUnipotent_comp
    (hpos : ∀ k, 0 < coPairing (ch (pos k)) ν) :
    positiveProductToUnipotent j hu ν hU hpos ≫ j.hom.hom = positiveProductMap u pos :=
  (exists_positiveProduct_lift j hu ν hU hpos).choose_spec

variable [IsAffine U.X.left] [IsOpenImmersion (cellMap i u neg pos).left]

include hu hU in
/-- An affine contracting group has an actual morphism of positive coordinates. -/
theorem exists_contractingCoordinatesMap
    (hneg : ∀ k, coPairing (ch (neg k)) ν < 0) :
    ∃ f : U.X ⟶ (VectorGroup.groupScheme (CommRingCat.of R) n).X,
      f ≫ positiveProductMap u pos = j.hom.hom := by
  have hj : j.hom.hom ∈
      (Dynamic.unipotent (AffineRegularBorel.cocharacter i ν)).carrier U.X := by
    rw [← hU.2]
    exact SubgroupFunctor.mem_range.mpr ⟨𝟙 _, Category.id_comp _⟩
  obtain ⟨c, hc⟩ := exists_orderedProduct_eq_of_mem_unipotent_of_affine (pos := pos)
    hu ν hneg j.hom.hom hj
  refine ⟨(VectorGroup.coordinates (CommRingCat.of R) n U.X).symm
    (Multiplicative.ofAdd c), ?_⟩
  rw [comp_positiveProductMap, MulEquiv.apply_symm_apply]
  exact hc.symm

/-- Positive coordinates as a scheme morphism on an affine contracting group. -/
def contractingCoordinatesMap (hneg : ∀ k, coPairing (ch (neg k)) ν < 0) :
    U.X ⟶ (VectorGroup.groupScheme (CommRingCat.of R) n).X :=
  (exists_contractingCoordinatesMap (pos := pos) j hu ν hU hneg).choose

/-- The coordinates reconstruct the actual subgroup inclusion. -/
theorem contractingCoordinatesMap_comp
    (hneg : ∀ k, coPairing (ch (neg k)) ν < 0) :
    contractingCoordinatesMap (pos := pos) j hu ν hU hneg ≫ positiveProductMap u pos =
      j.hom.hom :=
  (exists_contractingCoordinatesMap (pos := pos) j hu ν hU hneg).choose_spec

/-- Ordered positive-root multiplication is an isomorphism onto the actual contracting
scheme. The source is coordinate affine space; this is an isomorphism of schemes over
`Spec R`, and does not assert additivity of the multiplication law. -/
def positiveProductIso
    (hneg : ∀ k, coPairing (ch (neg k)) ν < 0)
    (hpos : ∀ k, 0 < coPairing (ch (pos k)) ν) :
    (VectorGroup.groupScheme (CommRingCat.of R) n).X ≅ U.X where
  hom := positiveProductToUnipotent j hu ν hU hpos
  inv := contractingCoordinatesMap (pos := pos) j hu ν hU hneg
  hom_inv_id := by
    let := positiveProductMap_mono (i := i) (u := u) (neg := neg) (pos := pos)
    apply (cancel_mono (positiveProductMap u pos)).mp
    rw [Category.assoc, contractingCoordinatesMap_comp,
      positiveProductToUnipotent_comp, Category.id_comp]
  inv_hom_id := by
    let := hU.1
    apply (cancel_mono j.hom.hom).mp
    rw [Category.assoc, positiveProductToUnipotent_comp,
      contractingCoordinatesMap_comp, Category.id_comp]

/-- The isomorphism is the actual ordered positive-root multiplication map. -/
theorem positiveProductIso_hom_comp
    (hneg : ∀ k, coPairing (ch (neg k)) ν < 0)
    (hpos : ∀ k, 0 < coPairing (ch (pos k)) ν) :
    (positiveProductIso j hu ν hU hneg hpos).hom ≫ j.hom.hom =
      positiveProductMap u pos :=
  positiveProductToUnipotent_comp j hu ν hU hpos

/-- The inverse isomorphism gives coordinates reconstructing the subgroup inclusion. -/
theorem positiveProductIso_inv_comp
    (hneg : ∀ k, coPairing (ch (neg k)) ν < 0)
    (hpos : ∀ k, 0 < coPairing (ch (pos k)) ν) :
    (positiveProductIso j hu ν hU hneg hpos).inv ≫ positiveProductMap u pos =
      j.hom.hom :=
  contractingCoordinatesMap_comp (pos := pos) j hu ν hU hneg

end Represented

end Langlands.GroupScheme.LocalSplitCell
