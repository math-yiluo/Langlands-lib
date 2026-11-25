/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleResolutionSectionCanonicalComparison
public import WeilConjectures.AlgebraicGeometry.EtaleLimitOpenCohomologyCocone
import WeilConjectures.AlgebraicGeometry.Curve.EtaleAdditiveCechCanonicalCoefficientTransfer
import WeilConjectures.AlgebraicGeometry.EtaleOpenObjectCohomologyPullback
import WeilConjectures.CategoryTheory.ExactFunctorResolutionCocycle
import Mathlib.CategoryTheory.Abelian.Injective.Resolution

/-! # A coefficient comparison of fixed normalized section complexes

Source: Stacks Project, Tag 0A50, functorial resolution proof, and Tag 01F7.
(blueprint: lem-weil-pbc-etale-section-short-complex-coefficient-comparison).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale


set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Extend the augmentation to a complex of injectives using successive exact images.
Source: Stacks Tag 01F7, Remark 20.14.2; the construction follows the proved private
helper in EtaleMayerVietorisSectionComparison and Mathlib's injective-resolution descent. -/
private theorem exists_lift_to_injective_complex
    {C : Type*} [Category* C] [Abelian C] {G : C} (I : InjectiveResolution G)
    (L : CochainComplex C ℕ) [∀ n, Injective (L.X n)]
    (f : G ⟶ L.X 0) (hf : f ≫ L.d 0 1 = 0) :
    ∃ α : I.cocomplex ⟶ L, I.ι.f 0 ≫ α.f 0 = f := by
  let a₀ : I.cocomplex.X 0 ⟶ L.X 0 := Injective.factorThru f (I.ι.f 0)
  have ha₀ : I.ι.f 0 ≫ a₀ = f := by simp [a₀]
  let a₁ : I.cocomplex.X 1 ⟶ L.X 1 :=
    I.exact₀.descToInjective (a₀ ≫ L.d 0 1) (by rw [← Category.assoc, ha₀, hf])
  have ha₁ : a₀ ≫ L.d 0 1 = I.cocomplex.d 0 1 ≫ a₁ := by
    exact (I.exact₀.comp_descToInjective _ _).symm
  let next (n : ℕ) (a : I.cocomplex.X n ⟶ L.X n)
      (b : I.cocomplex.X (n + 1) ⟶ L.X (n + 1))
      (h : a ≫ L.d n (n + 1) = I.cocomplex.d n (n + 1) ≫ b) :
      Σ' c : I.cocomplex.X (n + 2) ⟶ L.X (n + 2),
        b ≫ L.d (n + 1) (n + 2) = I.cocomplex.d (n + 1) (n + 2) ≫ c :=
    ⟨(I.exact_succ n).descToInjective (b ≫ L.d (n + 1) (n + 2))
      (by rw [← Category.assoc, ← h, Category.assoc, L.d_comp_d, comp_zero]),
      ((I.exact_succ n).comp_descToInjective _ _).symm⟩
  refine ⟨CochainComplex.mkHom I.cocomplex L a₀ a₁ ha₁
    (fun n ⟨a, b, h⟩ ↦ next n a b h), ?_⟩
  simpa only [CochainComplex.mkHom_f_0] using ha₀

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The open-section cocycle transfer, with the adjoint coefficient map retained.
Source: Stacks Tags 01FB and 03F3. Generalizes the proved calculation in
EtaleResolutionSectionTransferExtClass: exactFunctor_resolution_cocycle supplies
transport followed by the coefficient map; sectionsEquiv identifies its representative. -/
private theorem coefficient_transfer_ext
    {X Y : Scheme.{u}} (g : Y ⟶ X)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (I : InjectiveResolution G)
    (H : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (J : InjectiveResolution H)
    (ψ : G ⟶ (lowerStar AddCommGrpCat.{u + 1} g).obj H)
    (α : I.cocomplex ⟶
      ((lowerStar AddCommGrpCat.{u + 1} g).mapHomologicalComplex (.up ℕ)).obj J.cocomplex)
    (hα : I.ι.f 0 ≫ α.f 0 =
      ψ ≫ (lowerStar AddCommGrpCat.{u + 1} g).map (J.ι.f 0))
    (W : X.Opens) (q : ℕ)
    (fX : (etaleOpenFreeSheaf X).obj (Scheme.Etale.mk W.ι) ⟶ I.cocomplex.X q)
    (hfX : fX ≫ I.cocomplex.d q (q + 1) = 0)
    (fY : (etaleOpenFreeSheaf Y).obj (Scheme.Etale.mk (g ⁻¹ᵁ W).ι) ⟶ J.cocomplex.X q)
    (hfY : fY ≫ J.cocomplex.d q (q + 1) = 0)
    (hsections : EtaleOpenComparison.sectionsEquiv Y.smallEtaleTopology
      (Scheme.Etale.mk (g ⁻¹ᵁ W).ι) (J.cocomplex.X q) fY =
      (openResolutionSectionTransfer g I.cocomplex J.cocomplex α W).f q
        (EtaleOpenComparison.sectionsEquiv X.smallEtaleTopology
          (Scheme.Etale.mk W.ι) (I.cocomplex.X q) fX)) :
    J.extMk fY (q + 1) rfl hfY =
      (Abelian.Ext.mk₀ (etaleOpenFreeSheafPullback g W)).comp
        (((I.extMk fX (q + 1) rfl hfX).mapExactFunctor
          (upperStar AddCommGrpCat.{u + 1} g)).comp
            (Abelian.Ext.mk₀ (((upperStarLowerStarAdjunction _ g).homEquiv _ _).symm ψ))
            (add_zero q)) (zero_add q) := by
  let L := upperStar AddCommGrpCat.{u + 1} g
  let R := lowerStar AddCommGrpCat.{u + 1} g
  let adj := upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g
  let e : (L.mapHomologicalComplex (.up ℕ)).obj I.cocomplex ⟶ J.cocomplex :=
    { f := fun n ↦ (adj.homEquiv _ _).symm (α.f n)
      comm' := by
        intro n m _
        change (adj.homEquiv _ _).symm (α.f n) ≫ J.cocomplex.d n m =
          L.map (I.cocomplex.d n m) ≫ (adj.homEquiv _ _).symm (α.f m)
        apply (adj.homEquiv _ _).injective
        rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right]
        simpa using (α.comm n m) }
  let ψ' := (adj.homEquiv _ _).symm ψ
  have he : L.map (I.ι.f 0) ≫ e.f 0 = ψ' ≫ J.ι.f 0 := by
    apply (adj.homEquiv _ _).injective
    rw [Adjunction.homEquiv_naturality_left, Equiv.apply_symm_apply,
      Adjunction.homEquiv_naturality_right]
    change I.ι.f 0 ≫ α.f 0 = (adj.homEquiv G H) ((adj.homEquiv G H).symm ψ) ≫ _
    rw [Equiv.apply_symm_apply]
    exact hα
  have hc : (L.map fX ≫ e.f q) ≫ J.cocomplex.d q (q + 1) = 0 := by
    have hecomm := e.comm q (q + 1)
    change e.f q ≫ J.cocomplex.d q (q + 1) =
      L.map (I.cocomplex.d q (q + 1)) ≫ e.f (q + 1) at hecomm
    rw [Category.assoc, hecomm, ← L.map_comp_assoc, hfX, L.map_zero, zero_comp]
  have hfe : etaleOpenFreeSheafPullback g W ≫ (L.map fX ≫ e.f q) = fY := by
    apply (EtaleOpenComparison.sectionsEquiv Y.smallEtaleTopology
      (Scheme.Etale.mk (g ⁻¹ᵁ W).ι) (J.cocomplex.X q)).injective
    rw [EtaleOpenComparison.sectionsEquiv_naturality]
    dsimp only [etaleOpenFreeSheafPullback]
    rw [AddEquiv.apply_symm_apply]
    have hn : fX ≫ adj.unit.app (I.cocomplex.X q) =
        adj.unit.app _ ≫ R.map (L.map fX) := adj.unit.naturality fX
    have hαe : adj.unit.app (I.cocomplex.X q) ≫ R.map (e.f q) = α.f q :=
      (adj.homEquiv _ _).apply_symm_apply (α.f q)
    have hn' : adj.unit.app _ ≫ R.map (L.map fX ≫ e.f q) = fX ≫ α.f q := by
      rw [R.map_comp, ← Category.assoc, ← hn, Category.assoc, hαe]
    have hs := congrArg (EtaleOpenComparison.sectionsEquiv X.smallEtaleTopology
      (Scheme.Etale.mk W.ι) (R.obj (J.cocomplex.X q))) hn'
    rw [EtaleOpenComparison.sectionsEquiv_naturality,
      EtaleOpenComparison.sectionsEquiv_naturality] at hs
    rw [hsections]
    change (L.map fX ≫ e.f q).hom.app _
      (((L.obj _).obj.map (openSectionPullback g W).op)
        ((adj.unit.app _).hom.app _
          (EtaleOpenComparison.sectionsEquiv X.smallEtaleTopology
            (Scheme.Etale.mk W.ι) _ (𝟙 _)))) =
      (J.cocomplex.X q).obj.map (openSectionPullback g W).op
        ((α.f q).hom.app _
          (EtaleOpenComparison.sectionsEquiv X.smallEtaleTopology
            (Scheme.Etale.mk W.ι) _ fX))
    rw [NatTrans.naturality_apply]
    exact congrArg ((J.cocomplex.X q).obj.map (openSectionPullback g W).op) hs
  have hExt := exactFunctor_resolution_cocycle L ψ' I J e he q fX hfX hc
  rw [hExt, J.mk₀_comp_extMk]
  simp only [hfe]

set_option backward.isDefEq.respectTransparency.types false in
/-- A section cycle determines a closed Hom cocycle by the free-sheaf adjunction.
Source: Stacks Tags 03F3 and 0A50; the calculation is the one in
EtaleResolutionSectionCanonicalOpenTransfer. -/
private theorem section_cocycle
    {S : Scheme.{u}}
    (K : CochainComplex (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ)
    (W : S.Opens) (q : ℕ)
    (z : (((etaleSectionFunctor (Scheme.Etale.mk W.ι)).mapHomologicalComplex
      (.up ℕ)).obj K).cycles q) :
    let L := (((etaleSectionFunctor (Scheme.Etale.mk W.ι)).mapHomologicalComplex
      (.up ℕ)).obj K)
    let e := EtaleOpenComparison.sectionsEquiv S.smallEtaleTopology
      (Scheme.Etale.mk W.ι) (K.X q)
    e.symm (L.iCycles q z) ≫ K.d q (q + 1) = 0 := by
  dsimp only
  apply (EtaleOpenComparison.sectionsEquiv S.smallEtaleTopology
    (Scheme.Etale.mk W.ι) (K.X (q + 1))).injective
  rw [EtaleOpenComparison.sectionsEquiv_naturality, AddEquiv.apply_symm_apply,
    map_zero]
  let L := (((etaleSectionFunctor (Scheme.Etale.mk W.ι)).mapHomologicalComplex
    (.up ℕ)).obj K)
  exact ConcreteCategory.congr_hom (L.iCycles_d q (q + 1)) z

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The explicit open-object comparison respects coefficient morphisms.
Source: Stacks Tag 03F3; exact-functor preservation of Ext composition and associativity. -/
private theorem openObject_coefficient {X : Scheme.{u}} (W : X.Opens)
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (φ : F ⟶ G) (q : ℕ)
    (x : Abelian.Ext ((etaleOpenFreeSheaf X).obj (Scheme.Etale.mk W.ι)) F q) :
    etaleOpenObjectCohomologyMap G q W (x.comp (Abelian.Ext.mk₀ φ) (add_zero q)) =
      Sheaf.H.map ((upperStar AddCommGrpCat.{u + 1} W.ι).map φ) q
        (etaleOpenObjectCohomologyMap F q W x) := by
  change (Abelian.Ext.mk₀ (etaleOpenFreeSheafUnit W)).comp
    ((x.comp (Abelian.Ext.mk₀ φ) (add_zero q)).mapExactFunctor
      (upperStar AddCommGrpCat.{u + 1} W.ι)) (zero_add q) =
    ((Abelian.Ext.mk₀ (etaleOpenFreeSheafUnit W)).comp
      (x.mapExactFunctor (upperStar AddCommGrpCat.{u + 1} W.ι)) (zero_add q)).comp
        (Abelian.Ext.mk₀ ((upperStar AddCommGrpCat.{u + 1} W.ι).map φ)) (add_zero q)
  rw [Abelian.Ext.mapExactFunctor_comp, Abelian.Ext.mapExactFunctor_mk₀]
  exact (Abelian.Ext.comp_assoc_of_third_deg_zero _ _ _ _).symm

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Transfer on one open with arbitrary target coefficients and fixed comparisons.
Source: Stacks Tags 0A50, 01F7 and 03F3. Represent a class by a cycle, use the two
open_cocycle normalizations, and apply coefficient_transfer_ext followed by the
proved open-object pullback identity and coefficient naturality. -/
private theorem coefficient_transfer_open
    {X Y : Scheme.{u}} (g : Y ⟶ X)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (I : InjectiveResolution G)
    (H : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (J : InjectiveResolution H)
    (ψ : G ⟶ (lowerStar AddCommGrpCat.{u + 1} g).obj H)
    (α : I.cocomplex ⟶
      ((lowerStar AddCommGrpCat.{u + 1} g).mapHomologicalComplex (.up ℕ)).obj J.cocomplex)
    (hα : I.ι.f 0 ≫ α.f 0 =
      ψ ≫ (lowerStar AddCommGrpCat.{u + 1} g).map (J.ι.f 0))
    (cX : ResolutionSectionCanonicalComparison G I)
    (cY : ResolutionSectionCanonicalComparison H J) :
    ∀ W q x, cY.openEquiv (g ⁻¹ᵁ W) q (HomologicalComplex.homologyMap
      (openResolutionSectionTransfer g I.cocomplex J.cocomplex α W) q x) =
      Sheaf.H.map ((upperStar AddCommGrpCat.{u + 1} (g ⁻¹ᵁ W).ι).map
        (((upperStarLowerStarAdjunction _ g).homEquiv _ _).symm ψ)) q
        (openCohomologyPullback g W G q (cX.openEquiv W q x)) := by
  intro W q x
  let K := (((etaleSectionFunctor (Scheme.Etale.mk W.ι)).mapHomologicalComplex
    (.up ℕ)).obj I.cocomplex)
  let L := (((etaleSectionFunctor (Scheme.Etale.mk (g ⁻¹ᵁ W).ι)).mapHomologicalComplex
    (.up ℕ)).obj J.cocomplex)
  let φ := openResolutionSectionTransfer g I.cocomplex J.cocomplex α W
  have hs : Function.Surjective (K.homologyπ q) :=
    (AddCommGrpCat.epi_iff_surjective (K.homologyπ q)).mp inferInstance
  obtain ⟨z, rfl⟩ := hs x
  let zY := (HomologicalComplex.cyclesMap φ q) z
  let eX := EtaleOpenComparison.sectionsEquiv X.smallEtaleTopology
    (Scheme.Etale.mk W.ι) (I.cocomplex.X q)
  let eY := EtaleOpenComparison.sectionsEquiv Y.smallEtaleTopology
    (Scheme.Etale.mk (g ⁻¹ᵁ W).ι) (J.cocomplex.X q)
  let fX := eX.symm (K.iCycles q z)
  let fY := eY.symm (L.iCycles q zY)
  have hfX : fX ≫ I.cocomplex.d q (q + 1) = 0 :=
    section_cocycle I.cocomplex W q z
  have hfY : fY ≫ J.cocomplex.d q (q + 1) = 0 :=
    section_cocycle J.cocomplex (g ⁻¹ᵁ W) q zY
  have hmap : HomologicalComplex.homologyMap φ q (K.homologyπ q z) =
      L.homologyπ q zY :=
    congrArg (fun f => f z) (HomologicalComplex.homologyπ_naturality φ q)
  rw [hmap, cY.open_cocycle (g ⁻¹ᵁ W) q fY hfY zY
    (eY.apply_symm_apply _).symm,
    cX.open_cocycle W q fX hfX z (eX.apply_symm_apply _).symm]
  have hsections : eY fY = φ.f q (eX fX) := by
    change eY (eY.symm _) = φ.f q (eX (eX.symm _))
    rw [eY.apply_symm_apply, eX.apply_symm_apply]
    exact congrArg (fun f => f z) (HomologicalComplex.cyclesMap_i φ q)
  rw [coefficient_transfer_ext g G I H J ψ α hα W q fX hfX fY hfY hsections]
  rw [← Abelian.Ext.comp_assoc_of_third_deg_zero, openObject_coefficient,
    etaleOpenObjectCohomologyMap_pullback]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- A coefficient morphism induces a comparison of fixed section complexes.
Source: Stacks Project, Tag 0A50, resolution functoriality, and Tag 01F7.
(blueprint: lem-weil-pbc-etale-section-short-complex-coefficient-comparison)

Proof: Adjoint φ to F → f_*G. Inverse image is exact, so its right adjoint
preserves injectives. Extend the adjoint coefficient map from the augmentation
of I into f_*J in degree zero by injectivity. At each successor degree,
exactness of I makes the composite to the next term factor through the next
image, and injectivity extends this factor to the full resolution term.
This constructs an augmentation-preserving chain map I → f_*J. Apply
resolutionSectionShortComplexTransfer to it. Substitute hU and hV to identify
the target section complex with the one on the displayed target opens.
The equation hk and monicity of the source open inclusion identify k with
the restricted morphism f on the intersection.

For the whole-scheme homology map use the canonical coefficient transfer
identity, whose cocycle formula is normalized by cI and cJ. For the
intersection map represent a homology class by a cycle on U ∩ V. The
free-abelian-representable sections adjunction turns it into a Hom cocycle
into I. Exact inverse image followed by the adjoint chain map represents
pullback of its Ext class followed by φ. Evaluating its restriction on the
target intersection gives the transfer section. The two composition comparisons
along the square hk are exactly the first two factors of openSquareCoefficient;
restriction of φ gives its last factor. The open_cocycle fields of cI and cJ
therefore give the second identity. Homotopic lifts induce the same maps.
No covering hypothesis or connecting map is used. Zero coefficients, empty
opens, coincident opens and degree zero are included. -/
theorem etaleSectionShortComplex_coefficient_comparison
    {X Y : Scheme.{u}} (f : Y ⟶ X) (U V : X.Opens) (U' V' : Y.Opens)
    (hU : U' = f ⁻¹ᵁ U) (hV : V' = f ⁻¹ᵁ V)
    (k : (U' ⊓ V').toScheme ⟶ (U ⊓ V).toScheme)
    (hk : (U' ⊓ V').ι ≫ f = k ≫ (U ⊓ V).ι)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : (upperStar AddCommGrpCat.{u + 1} f).obj F ⟶ G)
    (I : InjectiveResolution F) (J : InjectiveResolution G)
    (cI : ResolutionSectionCanonicalComparison F I)
    (cJ : ResolutionSectionCanonicalComparison G J) :
    ∃ α : etaleSectionShortComplex U V I.cocomplex ⟶
        etaleSectionShortComplex U' V' J.cocomplex,
      (∀ (q : ℕ) (x : (etaleSectionShortComplex U V I.cocomplex).X₁.homology q),
        cJ.globalEquiv q (HomologicalComplex.homologyMap α.τ₁ q x) =
          Sheaf.H.map φ q (cohomologyMap f F q (cI.globalEquiv q x))) ∧
      (∀ (q : ℕ) (x : (etaleSectionShortComplex U V I.cocomplex).X₃.homology q),
        cJ.openEquiv (U' ⊓ V') q (HomologicalComplex.homologyMap α.τ₃ q x) =
          Sheaf.H.map (openSquareCoefficient f (U ⊓ V).ι (U' ⊓ V').ι k hk F G φ) q
            (cohomologyMap k ((upperStar AddCommGrpCat.{u + 1} (U ⊓ V).ι).obj F) q
              (cI.openEquiv (U ⊓ V) q x))) := by
  subst U'
  subst V'
  have hk' : k = f ∣_ (U ⊓ V) := by
    apply (cancel_mono (U ⊓ V).ι).1
    exact hk.symm.trans (morphismRestrict_ι f (U ⊓ V)).symm
  subst k
  let R := lowerStar AddCommGrpCat.{u + 1} f
  let L := (R.mapHomologicalComplex (.up ℕ)).obj J.cocomplex
  let adj := upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f
  have hinj (n : ℕ) : Injective (L.X n) :=
    adj.map_injective (J.cocomplex.X n) inferInstance
  let ψ := (adj.homEquiv F G) φ
  let a : F ⟶ L.X 0 := ψ ≫ R.map (J.ι.f 0)
  have ha : a ≫ L.d 0 1 = 0 := by
    change (ψ ≫ R.map (J.ι.f 0)) ≫ R.map (J.cocomplex.d 0 1) = 0
    rw [Category.assoc, ← R.map_comp, J.ι_f_zero_comp_complex_d, R.map_zero, comp_zero]
  obtain ⟨β, hβ⟩ := exists_lift_to_injective_complex I L a ha
  refine ⟨resolutionSectionShortComplexTransfer f U V I.cocomplex J.cocomplex β, ?_, ?_⟩
  · intro q x
    change cJ.globalEquiv q (HomologicalComplex.homologyMap
      (globalResolutionSectionTransfer f I.cocomplex J.cocomplex β) q x) = _
    simpa only [ψ, adj, Equiv.symm_apply_apply] using
      resolutionSection_canonical_coefficient_transfer f F I G J ψ β hβ cI cJ q x
  · intro q x
    have h := coefficient_transfer_open f F I G J ψ β hβ cI cJ (U ⊓ V) q x
    simp only [ψ, adj, Equiv.symm_apply_apply] at h
    change cJ.openEquiv (f ⁻¹ᵁ (U ⊓ V)) q
      (HomologicalComplex.homologyMap
        (openResolutionSectionTransfer f I.cocomplex J.cocomplex β (U ⊓ V)) q x) = _
    rw [h]
    dsimp only [openCohomologyPullback, AddMonoidHom.comp_apply, openSquareCoefficient,
      NatTrans.comp_app]
    change Sheaf.H.map _ q (Sheaf.H.map (_ ≫ _) q _) = _
    simp only [Sheaf.H.map_comp_apply]
    rfl

end AlgebraicGeometry.Etale
