import Langlands.HarmonicAnalysis.HarishChandraSchwartz.OpenCellIntegration
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.ParabolicHaar
import Langlands.GroupScheme.Absolute.OppositeCellProof
import Langlands.GroupScheme.Dynamic.AffineRepresentability
import Langlands.GroupScheme.Dynamic.SchemeDecomposition
import Langlands.AlgebraicGeometry.PointTopology.SchemeTopologyExistenceProofs
import Langlands.AlgebraicGeometry.PointTopology.RationalPointGroups
import Langlands.AlgebraicGeometry.PointTopology.RepresentedSubgroup
import Langlands.AlgebraicGeometry.PointTopology.SchemeProducts

/-! # The open cell on rational points

For a smooth affine group scheme `G` over a topological field `k` and a cocharacter `χ`, the
open-cell map `(p, v) ↦ p v⁻¹` from `P_G(χ)(k) × U_G(χ⁻¹)(k)` to `G(k)` is an open
embedding for the subspace topologies of the rational-point topology of `G(k)`. This is the
hypothesis `hι` of the open-cell integration formula (`OpenCellIntegration`) for actual
groups.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry Topology
open CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.HarishChandraSchwartz

section Generic

variable {G A B : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace A] [TopologicalSpace B] {P V : Subgroup G} {a : A → G} {b : B → G}

/-- If `(v, p) ↦ b v * a p` is an open embedding `B × A → G` and `a`, `b` have ranges `P`, `V`,
then `(p, v) ↦ p v⁻¹` is an open embedding `P × V → G` for the subspace topologies. -/
theorem isOpenEmbedding_openCellMap_of_mul (ha : Set.range a = P) (hb : Set.range b = V)
    (hΨ : IsOpenEmbedding (fun x : B × A => b x.1 * a x.2)) :
    IsOpenEmbedding (openCellMap (P := P) (V := V)) := by
  obtain ⟨v₀, hv₀⟩ : (1 : G) ∈ Set.range b := hb ▸ V.one_mem
  obtain ⟨p₀, hp₀⟩ : (1 : G) ∈ Set.range a := ha ▸ P.one_mem
  have hae : IsEmbedding a := by
    have h : a = (fun x : B × A => b x.1 * a x.2) ∘ Prod.mk v₀ := by
      funext p
      simp [hv₀]
    rw [h]
    exact hΨ.isEmbedding.comp (isEmbedding_prodMkRight v₀)
  have hbe : IsEmbedding b := by
    have h : b = (fun x : B × A => b x.1 * a x.2) ∘ (fun v => (v, p₀)) := by
      funext v
      simp [hp₀]
    rw [h]
    exact hΨ.isEmbedding.comp (isEmbedding_prodMkLeft p₀)
  let eA : A ≃ₜ P := hae.toHomeomorph.trans (Homeomorph.setCongr ha)
  let eB : B ≃ₜ V := hbe.toHomeomorph.trans (Homeomorph.setCongr hb)
  have heA : ∀ p : P, a (eA.symm p) = p := fun p =>
    congrArg Subtype.val (eA.apply_symm_apply p)
  have heB : ∀ v : V, b (eB.symm v) = v := fun v =>
    congrArg Subtype.val (eB.apply_symm_apply v)
  let e : P × V ≃ₜ B × A :=
    ((Homeomorph.inv P).prodCongr (Homeomorph.refl V)).trans
      ((eA.symm.prodCongr eB.symm).trans (Homeomorph.prodComm A B))
  have key : openCellMap (P := P) (V := V) =
      (Homeomorph.inv G) ∘ (fun x : B × A => b x.1 * a x.2) ∘ e := by
    funext x
    change (x.1 : G) * (x.2 : G)⁻¹ = (b (eB.symm x.2) * a (eA.symm x.1⁻¹))⁻¹
    rw [heA, heB, mul_inv_rev, Subgroup.coe_inv, inv_inv]
  rw [key]
  exact (Homeomorph.inv G).isOpenEmbedding.comp (hΨ.comp e.isOpenEmbedding)

omit [IsTopologicalGroup G] in
/-- If homeomorphisms `sU : A → U`, `sZ : B → M`, `sP : C → P`, `Φ : A × B → C` satisfy
`sP (Φ (a, b)) = sU a * sZ b`, then `(u, m) ↦ u m` is a homeomorphism `U × M → P`. -/
theorem isHomeomorph_mul_of_comp {A B C : Type*} [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalSpace C] {M U : Subgroup G} (hP' : ∀ x : U × M, (x.1 : G) * x.2 ∈ P)
    {sU : A → U} {sZ : B → M} {sP : C → P} {Φ : A × B → C} (hsU : IsHomeomorph sU)
    (hsZ : IsHomeomorph sZ) (hsP : IsHomeomorph sP) (hΦ : IsHomeomorph Φ)
    (h : ∀ a b, (sP (Φ (a, b)) : G) = sU a * sZ b) :
    IsHomeomorph (fun x : U × M => (⟨(x.1 : G) * x.2, hP' x⟩ : P)) := by
  let eU := hsU.homeomorph sU
  let eZ := hsZ.homeomorph sZ
  have key : (fun x : U × M => (⟨(x.1 : G) * x.2, hP' x⟩ : P)) =
      sP ∘ Φ ∘ Prod.map eU.symm eZ.symm := by
    funext x
    apply Subtype.ext
    change (x.1 : G) * x.2 = (sP (Φ (eU.symm x.1, eZ.symm x.2)) : G)
    rw [h]
    change (x.1 : G) * x.2 = (eU (eU.symm x.1) : G) * (eZ (eZ.symm x.2) : G)
    rw [eU.apply_symm_apply, eZ.apply_symm_apply]
  rw [key]
  exact hsP.comp (hΦ.comp (eU.symm.isHomeomorph.prodMap eZ.symm.isHomeomorph))

/-- If `(u, m) ↦ u m` is a homeomorphism `U × M → P` onto a subgroup `P`, then so is
`(m, u) ↦ m u`. -/
theorem isHomeomorph_mul_of_isHomeomorph_mul_swap {M U : Subgroup G}
    (hP : ∀ x : M × U, (x.1 : G) * x.2 ∈ P) (hP' : ∀ x : U × M, (x.1 : G) * x.2 ∈ P)
    (h : IsHomeomorph (fun x : U × M => (⟨(x.1 : G) * x.2, hP' x⟩ : P))) :
    IsHomeomorph (fun x : M × U => (⟨(x.1 : G) * x.2, hP x⟩ : P)) := by
  have key : (fun x : M × U => (⟨(x.1 : G) * x.2, hP x⟩ : P)) =
      (Homeomorph.inv P) ∘ (fun x : U × M => (⟨(x.1 : G) * x.2, hP' x⟩ : P)) ∘
        Prod.map (Homeomorph.inv U) (Homeomorph.inv M) ∘ (Homeomorph.prodComm M U) := by
    funext x
    apply Subtype.ext
    simp [mul_inv_rev]
  rw [key]
  exact (Homeomorph.inv P).isHomeomorph.comp (h.comp
    (((Homeomorph.inv U).isHomeomorph.prodMap (Homeomorph.inv M).isHomeomorph).comp
      (Homeomorph.prodComm M U).isHomeomorph))

end Generic

section Scheme

variable (k : Type u) [Field k] [TopologicalSpace k] [IsTopologicalRing k] [IsOpenUnits k]

/-- Points of a product over `Spec k` are pairs of points, homeomorphically for the
scheme-point topologies: the inverse of the published `schemeProductPointHomeomorph` for
`R = S = k`. -/
def productPointHomeomorph (X Y : Over (Spec (CommRingCat.of k))) :
    letI : TopologicalSpace (RingPoint k X k) := schemePointTopology k X k
    letI : TopologicalSpace (RingPoint k Y k) := schemePointTopology k Y k
    letI : TopologicalSpace (RingPoint k (X ⊗ Y) k) := schemePointTopology k (X ⊗ Y) k
    RingPoint k X k × RingPoint k Y k ≃ₜ RingPoint k (X ⊗ Y) k := by
  letI : TopologicalSpace (RingPoint k X k) := schemePointTopology k X k
  letI : TopologicalSpace (RingPoint k Y k) := schemePointTopology k Y k
  letI : TopologicalSpace (RingPoint k (X ⊗ Y) k) := schemePointTopology k (X ⊗ Y) k
  exact (schemeProductPointHomeomorph k k X Y).symm

theorem productPointHomeomorph_apply (X Y : Over (Spec (CommRingCat.of k)))
    (x : RingPoint k X k × RingPoint k Y k) :
    (productPointHomeomorph k X Y x : RingPoint k (X ⊗ Y) k) = lift x.1 x.2 :=
  schemeProductPointHomeomorph_symm_apply k k X Y x

/-- On an affine scheme, rational points with the rational-point topology are homeomorphic to
base-valued points with the scheme-point topology. -/
def rationalPointSchemeHomeomorph (X : Over (Spec (CommRingCat.of k))) [IsAffine X.left] :
    letI : TopologicalSpace (RationalPoint k X) := rationalPointTopology k X
    letI : TopologicalSpace (RingPoint k X k) := schemePointTopology k X k
    RationalPoint k X ≃ₜ RingPoint k X k := by
  letI : TopologicalSpace (RationalPoint k X) := rationalPointTopology k X
  have h := schemePointTopology_eq_affine k X k
  exact @Homeomorph.mk _ _ (rationalPointTopology k X) (schemePointTopology k X k)
    (rationalPointEquiv k X) (continuous_le_rng h.ge (rationalPointHomeomorph k X).continuous)
    (continuous_le_dom h.le (rationalPointHomeomorph k X).symm.continuous)

omit [TopologicalSpace k] [IsTopologicalRing k] [IsOpenUnits k] in
theorem rationalPointEquiv_eq_comp {X : Over (Spec (CommRingCat.of k))}
    (p : RationalPoint k X) :
    (rationalPointEquiv k X p : ringTest k k ⟶ X) = (ringTestSelfIso k).hom ≫ p := by
  change (ringTestSelfIso k).symm.inv ≫ p ≫ (Iso.refl X).hom = _
  simp

/-- If the multiplication `U × P → G`, `(u, p) ↦ iU(u) iP(p)`, of affine group schemes over a
topological field is an open immersion, then it is an open embedding on rational points for the
rational-point topologies. -/
theorem isOpenEmbedding_rationalPoint_mul {G U P : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffine G.X.left] [IsAffine U.X.left] [IsAffine P.X.left] (iU : U ⟶ G) (iP : P ⟶ G)
    (hm : IsOpenImmersion ((fst U.X P.X ≫ iU.hom.hom) * (snd U.X P.X ≫ iP.hom.hom)).left) :
    letI : TopologicalSpace (RationalPoint k G.X) := rationalPointTopology k G.X
    letI : TopologicalSpace (RationalPoint k U.X) := rationalPointTopology k U.X
    letI : TopologicalSpace (RationalPoint k P.X) := rationalPointTopology k P.X
    IsOpenEmbedding (fun x : RationalPoint k U.X × RationalPoint k P.X =>
      (x.1 ≫ iU.hom.hom) * (x.2 ≫ iP.hom.hom)) := by
  let : TopologicalSpace (RationalPoint k G.X) := rationalPointTopology k G.X
  let : TopologicalSpace (RationalPoint k U.X) := rationalPointTopology k U.X
  let : TopologicalSpace (RationalPoint k P.X) := rationalPointTopology k P.X
  let : TopologicalSpace (RingPoint k U.X k) := schemePointTopology k U.X k
  let : TopologicalSpace (RingPoint k P.X k) := schemePointTopology k P.X k
  let : TopologicalSpace (RingPoint k (U.X ⊗ P.X) k) := schemePointTopology k (U.X ⊗ P.X) k
  let : TopologicalSpace (RingPoint k G.X k) := schemePointTopology k G.X k
  let m := (fst U.X P.X ≫ iU.hom.hom) * (snd U.X P.X ≫ iP.hom.hom)
  have : IsOpenImmersion m.left := hm
  have hO := isOpenEmbedding_schemePointMap k k m
  let eU := rationalPointSchemeHomeomorph k U.X
  let eP := rationalPointSchemeHomeomorph k P.X
  let eG := rationalPointSchemeHomeomorph k G.X
  have key : (fun x : RationalPoint k U.X × RationalPoint k P.X =>
      (x.1 ≫ iU.hom.hom) * (x.2 ≫ iP.hom.hom)) =
      eG.symm ∘ (fun q : RingPoint k (U.X ⊗ P.X) k => (q ≫ m : RingPoint k G.X k)) ∘
        productPointHomeomorph k U.X P.X ∘ (eU.prodCongr eP) := by
    funext x
    apply (rationalPointEquiv k G.X).injective
    have h1 : (eG.symm ∘ (fun q : RingPoint k (U.X ⊗ P.X) k => (q ≫ m : RingPoint k G.X k)) ∘
        productPointHomeomorph k U.X P.X ∘ (eU.prodCongr eP)) x =
        (rationalPointEquiv k G.X).symm
          (lift (rationalPointEquiv k U.X x.1) (rationalPointEquiv k P.X x.2) ≫ m) := by
      change eG.symm (productPointHomeomorph k U.X P.X (eU.prodCongr eP x) ≫ m) = _
      rw [productPointHomeomorph_apply]
      rfl
    rw [h1]
    refine Eq.trans ?_ (Equiv.apply_symm_apply (rationalPointEquiv k G.X) _).symm
    refine (rationalPointEquiv_eq_comp k _).trans ?_
    simp only [rationalPointEquiv_eq_comp, m, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc,
      Category.assoc]
    rfl
  rw [key]
  exact eG.symm.isOpenEmbedding.comp
    (hO.comp ((productPointHomeomorph k U.X P.X).isOpenEmbedding.comp
      (eU.prodCongr eP).isOpenEmbedding))

open Langlands.GroupScheme in
/-- **The open cell on rational points.** For a smooth affine group scheme `G` over a topological
field `k` with open units and a cocharacter `χ : 𝔾_m ⟶ G`, the open-cell map
`P_G(χ)(k) × U_G(χ⁻¹)(k) → G(k)`, `(p, v) ↦ p v⁻¹`, is an open embedding for the subspace
topologies of the rational-point topology of `G(k)`. -/
theorem isOpenEmbedding_openCellMap_rationalPoint (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffine G.X.left] (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) :
    letI : TopologicalSpace (RationalPoint k G.X) := rationalPointTopology k G.X
    IsOpenEmbedding (openCellMap
      (P := (Dynamic.parabolic χ).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))))
      (V := (Dynamic.unipotent (CommGroupScheme.groupHom
        (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫ χ)).carrier
          (Over.mk (𝟙 (Spec (CommRingCat.of k)))))) := by
  let : TopologicalSpace (RationalPoint k G.X) := rationalPointTopology k G.X
  let : IsTopologicalGroup (RationalPoint k G.X) := rationalPoint_isTopologicalGroup k G
  set χ' := CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫ χ
  have hU := Dynamic.Affine.isRepresentedBy_unipotentHom χ'
  have hP := Dynamic.Affine.isRepresentedBy_parabolicHom χ
  have : IsClosedImmersion (Dynamic.Affine.unipotentHom χ').hom.hom.left :=
    Dynamic.Affine.isClosedSubgroup_unipotentHom χ'
  have : IsClosedImmersion (Dynamic.Affine.parabolicHom χ).hom.hom.left :=
    Dynamic.Affine.isClosedSubgroup_parabolicHom χ
  have : IsAffine (Dynamic.Affine.unipotentScheme χ').X.left :=
    isAffine_of_isAffineHom (Dynamic.Affine.unipotentHom χ').hom.hom.left
  have : IsAffine (Dynamic.Affine.parabolicScheme χ).X.left :=
    isAffine_of_isAffineHom (Dynamic.Affine.parabolicHom χ).hom.hom.left
  have hm := oppositeCellStatement k G χ _ _ _ _ hU hP
  let : TopologicalSpace (RationalPoint k (Dynamic.Affine.unipotentScheme χ').X) :=
    rationalPointTopology k _
  let : TopologicalSpace (RationalPoint k (Dynamic.Affine.parabolicScheme χ).X) :=
    rationalPointTopology k _
  refine isOpenEmbedding_openCellMap_of_mul
    (a := fun p : RationalPoint k (Dynamic.Affine.parabolicScheme χ).X =>
      p ≫ (Dynamic.Affine.parabolicHom χ).hom.hom)
    (b := fun u : RationalPoint k (Dynamic.Affine.unipotentScheme χ').X =>
      u ≫ (Dynamic.Affine.unipotentHom χ').hom.hom) ?_ ?_
    (isOpenEmbedding_rationalPoint_mul k _ _ hm)
  · rw [← hP.2]
    rfl
  · rw [← hU.2]
    rfl

/-- An isomorphism `X ⊗ Y ≅ Z` of affine schemes over `Spec k` induces a homeomorphism
`X(k) × Y(k) ≃ₜ Z(k)` for the rational-point topologies. -/
def rationalPointProdHomeomorph {X Y Z : Over (Spec (CommRingCat.of k))} [IsAffine X.left]
    [IsAffine Y.left] [IsAffine Z.left] (e : X ⊗ Y ≅ Z) :
    letI : TopologicalSpace (RationalPoint k X) := rationalPointTopology k X
    letI : TopologicalSpace (RationalPoint k Y) := rationalPointTopology k Y
    letI : TopologicalSpace (RationalPoint k Z) := rationalPointTopology k Z
    RationalPoint k X × RationalPoint k Y ≃ₜ RationalPoint k Z := by
  letI : TopologicalSpace (RationalPoint k X) := rationalPointTopology k X
  letI : TopologicalSpace (RationalPoint k Y) := rationalPointTopology k Y
  letI : TopologicalSpace (RationalPoint k Z) := rationalPointTopology k Z
  letI : TopologicalSpace (RingPoint k X k) := schemePointTopology k X k
  letI : TopologicalSpace (RingPoint k Y k) := schemePointTopology k Y k
  letI : TopologicalSpace (RingPoint k (X ⊗ Y) k) := schemePointTopology k (X ⊗ Y) k
  letI : TopologicalSpace (RingPoint k Z k) := schemePointTopology k Z k
  exact ((rationalPointSchemeHomeomorph k X).prodCongr (rationalPointSchemeHomeomorph k Y)).trans
    ((productPointHomeomorph k X Y).trans
      ((schemePointIsoHomeomorph k k e).trans (rationalPointSchemeHomeomorph k Z).symm))

theorem ringTestSelfIso_comp_rationalPointProdHomeomorph {X Y Z : Over (Spec (CommRingCat.of k))}
    [IsAffine X.left] [IsAffine Y.left] [IsAffine Z.left] (e : X ⊗ Y ≅ Z)
    (x : RationalPoint k X × RationalPoint k Y) :
    (ringTestSelfIso k).hom ≫ rationalPointProdHomeomorph k e x =
      lift ((ringTestSelfIso k).hom ≫ x.1) ((ringTestSelfIso k).hom ≫ x.2) ≫ e.hom := by
  rw [← rationalPointEquiv_eq_comp, ← rationalPointEquiv_eq_comp, ← rationalPointEquiv_eq_comp]
  change rationalPointEquiv k Z ((rationalPointEquiv k Z).symm (productPointHomeomorph k X Y
    (rationalPointEquiv k X x.1, rationalPointEquiv k Y x.2) ≫ e.hom)) = _
  refine (Equiv.apply_symm_apply (rationalPointEquiv k Z) _).trans ?_
  exact congrArg (fun q : RingPoint k (X ⊗ Y) k => (q ≫ e.hom : RingPoint k Z k))
    (productPointHomeomorph_apply k X Y _)

open Langlands.GroupScheme in
/-- On rational points, the Levi multiplication isomorphism `U_G(χ) ⊗ Z_G(χ) ≅ P_G(χ)` is
`(u, z) ↦ u z`. -/
theorem rationalPointProdHomeomorph_multiplicationIso_comp
    {G U Z P : GroupScheme (Spec (CommRingCat.of k))} [IsSeparated G.X.hom]
    {χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G} {iP : P ⟶ G} {iZ : Z ⟶ G} {iU : U ⟶ G}
    (hP : (Dynamic.parabolic χ).IsRepresentedBy iP)
    (hZ : (Dynamic.centralizer χ).IsRepresentedBy iZ)
    (hU : (Dynamic.unipotent χ).IsRepresentedBy iU)
    [IsAffine U.X.left] [IsAffine Z.X.left] [IsAffine P.X.left]
    (x : RationalPoint k U.X × RationalPoint k Z.X) :
    rationalPointProdHomeomorph k (Dynamic.multiplicationIso hP hZ hU) x ≫ iP.hom.hom =
      (x.1 ≫ iU.hom.hom) * (x.2 ≫ iZ.hom.hom) := by
  apply (cancel_epi (ringTestSelfIso k).hom).mp
  rw [reassoc_of% (ringTestSelfIso_comp_rationalPointProdHomeomorph k _ x)]
  change lift _ _ ≫ (Dynamic.multiplication hP hZ hU ≫ _) = _
  rw [Dynamic.multiplication_comp]
  simp only [MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc]
  rfl

open Langlands.GroupScheme in
/-- If closed subgroup schemes `P`, `Z`, `U` of an affine group scheme `G` over a topological
field `k` represent `P_G(χ)`, `Z_G(χ)`, `U_G(χ)`, then `(m, u) ↦ m u` is a homeomorphism
`Z_G(χ)(k) × U_G(χ)(k) → P_G(χ)(k)` for the subspace topologies of the rational-point topology
of `G(k)`. -/
theorem isHomeomorph_leviUnipotentMul_of_isRepresentedBy
    {G U Z P : GroupScheme (Spec (CommRingCat.of k))} [LocallyOfFiniteType G.X.hom]
    [IsAffine G.X.left] {χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G}
    {iP : P ⟶ G} {iZ : Z ⟶ G} {iU : U ⟶ G}
    (hP : (Dynamic.parabolic χ).IsRepresentedBy iP)
    (hZ : (Dynamic.centralizer χ).IsRepresentedBy iZ)
    (hU : (Dynamic.unipotent χ).IsRepresentedBy iU)
    (cP : IsClosedSubgroup iP) (cZ : IsClosedSubgroup iZ) (cU : IsClosedSubgroup iU) :
    letI : TopologicalSpace (RationalPoint k G.X) := rationalPointTopology k G.X
    IsHomeomorph (fun x : (Dynamic.centralizer χ).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) ×
        (Dynamic.unipotent χ).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) =>
      (⟨(x.1 : RationalPoint k G.X) * x.2, mul_mem (Dynamic.centralizer_le_parabolic χ _ x.1.2)
        (Dynamic.unipotent_le_parabolic χ _ x.2.2)⟩ :
        (Dynamic.parabolic χ).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))))) := by
  let : TopologicalSpace (RationalPoint k G.X) := rationalPointTopology k G.X
  let : IsTopologicalGroup (RationalPoint k G.X) := rationalPoint_isTopologicalGroup k G
  have : IsAffineHom G.X.hom := isAffineHom_of_isAffine _
  have : IsClosedImmersion iP.hom.hom.left := cP
  have : IsClosedImmersion iZ.hom.hom.left := cZ
  have : IsClosedImmersion iU.hom.hom.left := cU
  have : IsAffine P.X.left := isAffine_of_isAffineHom iP.hom.hom.left
  have : IsAffine Z.X.left := isAffine_of_isAffineHom iZ.hom.hom.left
  have : IsAffine U.X.left := isAffine_of_isAffineHom iU.hom.hom.left
  let : TopologicalSpace (RationalPoint k P.X) := rationalPointTopology k _
  let : TopologicalSpace (RationalPoint k Z.X) := rationalPointTopology k _
  let : TopologicalSpace (RationalPoint k U.X) := rationalPointTopology k _
  -- `(u, z) ↦ u z`, transported to the subgroups of `G(k)`
  let sU := rationalPointSubgroupHomeomorph k (Dynamic.unipotent χ) _ hU cU
  let sZ := rationalPointSubgroupHomeomorph k (Dynamic.centralizer χ) _ hZ cZ
  let sP := rationalPointSubgroupHomeomorph k (Dynamic.parabolic χ) _ hP cP
  have hsU : ∀ p, (sU p : RationalPoint k G.X) = p ≫ iU.hom.hom :=
    rationalPointSubgroupHomeomorph_apply_coe k _ _ hU cU
  have hsZ : ∀ p, (sZ p : RationalPoint k G.X) = p ≫ iZ.hom.hom :=
    rationalPointSubgroupHomeomorph_apply_coe k _ _ hZ cZ
  have hsP : ∀ p, (sP p : RationalPoint k G.X) = p ≫ iP.hom.hom :=
    rationalPointSubgroupHomeomorph_apply_coe k _ _ hP cP
  let Φ := rationalPointProdHomeomorph k (Dynamic.multiplicationIso hP hZ hU)
  have hΦ : ∀ x, Φ x ≫ iP.hom.hom = (x.1 ≫ iU.hom.hom) * (x.2 ≫ iZ.hom.hom) :=
    rationalPointProdHomeomorph_multiplicationIso_comp k hP hZ hU
  clear_value sU sZ sP Φ
  have hsU' : IsHomeomorph sU := sU.toHomeomorph.isHomeomorph
  have hsZ' : IsHomeomorph sZ := sZ.toHomeomorph.isHomeomorph
  have hsP' : IsHomeomorph sP := sP.toHomeomorph.isHomeomorph
  have hP' : ∀ x : (Dynamic.unipotent χ).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) ×
      (Dynamic.centralizer χ).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))),
      (x.1 : RationalPoint k G.X) * x.2 ∈
        (Dynamic.parabolic χ).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) := fun x =>
    mul_mem (Dynamic.unipotent_le_parabolic χ _ x.1.2) (Dynamic.centralizer_le_parabolic χ _ x.2.2)
  -- `(u, z) ↦ u z` on the subgroups of `G(k)`
  have h0 := isHomeomorph_mul_of_comp hP' hsU' hsZ' hsP' Φ.isHomeomorph (fun a b => by
    rw [hsP, hΦ, hsU, hsZ])
  exact isHomeomorph_mul_of_isHomeomorph_mul_swap (fun x => mul_mem
    (Dynamic.centralizer_le_parabolic χ _ x.1.2) (Dynamic.unipotent_le_parabolic χ _ x.2.2)) hP' h0

open Langlands.GroupScheme in
/-- **The Levi decomposition on rational points.** For an affine group scheme `G` over a
topological field `k` with open units and a cocharacter `χ : 𝔾_m ⟶ G`, the map
`Z_G(χ)(k) × U_G(χ)(k) → P_G(χ)(k)`, `(m, u) ↦ m u`, is a homeomorphism for the subspace
topologies of the rational-point topology of `G(k)`. -/
theorem isHomeomorph_leviUnipotentMul_rationalPoint (G : GroupScheme (Spec (CommRingCat.of k)))
    [LocallyOfFiniteType G.X.hom] [IsAffine G.X.left]
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) :
    letI : TopologicalSpace (RationalPoint k G.X) := rationalPointTopology k G.X
    IsHomeomorph (fun x : (Dynamic.centralizer χ).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) ×
        (Dynamic.unipotent χ).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) =>
      (⟨(x.1 : RationalPoint k G.X) * x.2, mul_mem (Dynamic.centralizer_le_parabolic χ _ x.1.2)
        (Dynamic.unipotent_le_parabolic χ _ x.2.2)⟩ :
        (Dynamic.parabolic χ).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))))) :=
  isHomeomorph_leviUnipotentMul_of_isRepresentedBy k
    (Dynamic.Affine.isRepresentedBy_parabolicHom χ)
    (Dynamic.Affine.isRepresentedBy_centralizerHom χ)
    (Dynamic.Affine.isRepresentedBy_unipotentHom χ)
    (Dynamic.Affine.isClosedSubgroup_parabolicHom χ)
    (Dynamic.Affine.isClosedSubgroup_centralizerHom χ)
    (Dynamic.Affine.isClosedSubgroup_unipotentHom χ)

open Langlands.GroupScheme in
/-- The hypothesis `hhomeo` of `leviUnipotentMeasure_isHaarMeasure` for
`P_G(χ)(k) = Z_G(χ)(k) U_G(χ)(k)`: the coordinates `leviUnipotentCoord` are a homeomorphism. -/
theorem isHomeomorph_leviUnipotentCoord_rationalPoint (G : GroupScheme (Spec (CommRingCat.of k)))
    [LocallyOfFiniteType G.X.hom] [IsAffine G.X.left]
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) :
    letI : TopologicalSpace (RationalPoint k G.X) := rationalPointTopology k G.X
    letI : IsTopologicalGroup (RationalPoint k G.X) := rationalPoint_isTopologicalGroup k G
    IsHomeomorph (leviUnipotentCoord
      (M := (Dynamic.centralizer χ).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))))
      (U := (Dynamic.unipotent χ).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))))
      (P := (Dynamic.parabolic χ).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))))
      (fun x => mul_mem (Dynamic.centralizer_le_parabolic χ _ x.1.2)
        (Dynamic.unipotent_le_parabolic χ _ x.2.2))) :=
  isHomeomorph_leviUnipotentMul_rationalPoint k G χ

end Scheme

end Langlands.HarishChandraSchwartz
