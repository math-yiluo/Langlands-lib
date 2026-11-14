import Langlands.GroupScheme.Rational.NonreductiveRootProducts
import Langlands.GroupScheme.Torus.LocalRootRayComparison
import Langlands.GroupScheme.Rational.OrderedProductBaseChange
import Langlands.GroupScheme.Rational.RootSubgroupBaseChange
import Langlands.GroupScheme.Rational.CrossTorusRootTransport
import Langlands.GroupScheme.Rational.RootSubgroupPositive
import Langlands.GroupScheme.Dynamic.RingSmoothConnectedProof
import Langlands.GroupScheme.Rational.StandardRepresentability
import Langlands.GroupScheme.SmoothProducts
import Langlands.AlgebraicGeometry.FiberwiseOpenImmersion

/-! # Integral ordered root products over a local base -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.RelativeRoot

section ArbitraryBase

variable {B B' : Scheme.{u}} (I : Type u) [Fintype I]
    {G : GroupScheme B} (i : splitTorus B I ⟶ G)

/-- Fixed-exponent root functors commute with base change through the
specified coordinate-torus isomorphism. -/
theorem exponentRoot_subgroup_baseChange (b : B' ⟶ B) (m : I → ℤ) :
    subgroup ((splitTorus.baseChangeIso b I).inv ≫ (GroupScheme.baseChange b).map i)
        (splitTorus.exponentCharacter B' I m) =
      (subgroup i (splitTorus.exponentCharacter B I m)).baseChange b := by
  have hsq : (GroupScheme.baseChange b).map i ≫
      (Iso.refl ((GroupScheme.baseChange b).obj G)).hom =
      CommGroupScheme.groupHom (splitTorus.commBaseChangeIso b I).hom ≫
        ((splitTorus.baseChangeIso b I).inv ≫ (GroupScheme.baseChange b).map i) := by
    change _ ≫ 𝟙 _ = (splitTorus.baseChangeIso b I).hom ≫
      (splitTorus.baseChangeIso b I).inv ≫ _
    rw [Category.comp_id, Iso.hom_inv_id_assoc]
  have htr := subgroup_comap_of_transport (splitTorus.commBaseChangeIso b I)
    (Iso.refl _) hsq
    (characterLattice.baseChange b _ (splitTorus.exponentCharacter B I m))
  have ha : characterLattice.congr (splitTorus.commBaseChangeIso b I)
      (characterLattice.baseChange b _ (splitTorus.exponentCharacter B I m)) =
      splitTorus.exponentCharacter B' I m := by
    rw [characterLattice.congr_apply, ← splitTorus.exponentCharacter_baseChange,
      Iso.inv_hom_id_assoc]
  rw [ha, Iso.refl_hom, SubgroupFunctor.comap_id] at htr
  exact htr.trans (subgroup_baseChange
    (S := splitTorus.commGroupScheme B I) b i (splitTorus.exponentCharacter B I m))

/-- Positive integer exponent pairing gives containment of the actual root
functor in the actual dynamic radical over any base scheme. -/
theorem exponentRoot_le_dynamicUnipotent (m ν : I → ℤ)
    (hpos : 0 < ∑ j, m j * ν j) :
    subgroup i (splitTorus.exponentCharacter B I m) ≤
      Dynamic.unipotent
        (CommGroupScheme.groupHom (splitTorus.exponentCocharacter B I ν) ≫ i) := by
  apply subgroup_le_dynamicUnipotent_of_power i _
    (splitTorus.exponentCocharacter B I ν)
    (show 0 < (∑ j, m j * ν j).toNat by omega)
  rw [splitTorus.exponentCocharacter_comp_exponentCharacter,
    Int.toNat_of_nonneg hpos.le]

end ArbitraryBase

private theorem isIso_of_residueField_fibres
    {B : Scheme.{u}} {X Y : Over B} (f : X ⟶ Y)
    [Flat X.hom] [LocallyOfFinitePresentation X.hom] [LocallyOfFiniteType Y.hom]
    (hf : ∀ s : B, IsIso ((Over.pullback (B.fromSpecResidueField s)).map f)) :
    IsIso f := by
  have : IsOpenImmersion f.left :=
    Langlands.AlgebraicGeometry.isOpenImmersion_of_fiberwise f fun s => by
      let := hf s
      exact inferInstanceAs
        (IsOpenImmersion (((Over.forget _).map
          ((Over.pullback (B.fromSpecResidueField s)).map f))))
  have : Surjective f.left := by
    refine ⟨fun y => ?_⟩
    let s : B := Y.hom y
    obtain ⟨y', hy', -⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := Y.hom) (g := B.fromSpecResidueField s) y
      (IsLocalRing.closedPoint (B.residueField s))
      (Scheme.fromSpecResidueField_apply _ _).symm
    let := hf s
    have : IsIso ((Over.pullback (B.fromSpecResidueField s)).map f).left :=
      Functor.map_isIso (Over.forget (Spec (B.residueField s)))
        ((Over.pullback (B.fromSpecResidueField s)).map f)
    obtain ⟨x', hx'⟩ :=
      (((Over.pullback (B.fromSpecResidueField s)).map f).left).surjective y'
    have hcomp : pullback.fst X.hom (B.fromSpecResidueField s) ≫ f.left =
        ((Over.pullback (B.fromSpecResidueField s)).map f).left ≫
          pullback.fst Y.hom (B.fromSpecResidueField s) :=
      (pullback.lift_fst _ _ _).symm
    refine ⟨pullback.fst X.hom (B.fromSpecResidueField s) x', ?_⟩
    rw [← hy', ← hx']
    change (pullback.fst X.hom (B.fromSpecResidueField s) ≫ f.left) x' =
      (((Over.pullback (B.fromSpecResidueField s)).map f).left ≫
        pullback.fst Y.hom (B.fromSpecResidueField s)) x'
    exact congrArg (fun a => a x') hcomp
  have : IsIso f.left :=
    (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨inferInstance, inferInstance⟩
  have : IsIso ((Over.forget B).map f) := ‹IsIso f.left›
  exact isIso_of_reflects_iso f (Over.forget B)

section LocalRing

variable {R k : Type u} [CommRing R] [IsLocalRing R] [Field k] [Algebra R k]
    (I : Type u) [Fintype I] [DecidableEq I]
    {G : GroupScheme (Spec (CommRingCat.of R))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [GeometricallyConnected G.X.hom]
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G) (ν : I → ℤ)

local instance localRootProductAffine {A : Type u} [CommRing A] [Algebra R A] :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap R A)).obj G).X.hom :=
  inferInstanceAs (IsAffineHom (pullback.snd G.X.hom (algebraBaseMap R A)))

set_option maxHeartbeats 1600000 in
/-- Supplied ordered integral root factors give the actual dynamic product
on every field-valued fibre, once one fibre has disjoint positive rays. -/
theorem isIso_orderedRootProduct_fieldFibre
    (hdisj : ∀ a ∈ indivisiblePositiveRoots (splitTorus.baseChangeHom (K := k) G I i)
        (splitTorus.exponentCocharacter (Spec (CommRingCat.of k)) I ν),
      ∀ b ∈ indivisiblePositiveRoots (splitTorus.baseChangeHom (K := k) G I i)
        (splitTorus.exponentCocharacter (Spec (CommRingCat.of k)) I ν), a ≠ b →
        Disjoint (cyclicTail a 1 :
          Set (characterLattice (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I)))
          (cyclicTail b 1 :
            Set (characterLattice (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I))))
    {n : ℕ} (m : Fin n → I → ℤ)
    (hinj : Function.Injective (fun r =>
      splitTorus.exponentCharacter (Spec (CommRingCat.of k)) I (m r)))
    (ha : Set.range (fun r =>
        splitTorus.exponentCharacter (Spec (CommRingCat.of k)) I (m r)) =
      indivisiblePositiveRoots (splitTorus.baseChangeHom (K := k) G I i)
        (splitTorus.exponentCocharacter (Spec (CommRingCat.of k)) I ν))
    {U : GroupScheme (Spec (CommRingCat.of R))} {jU : U ⟶ G}
    (hU : (Dynamic.unipotent
      (CommGroupScheme.groupHom
        (splitTorus.exponentCocharacter (Spec (CommRingCat.of R)) I ν) ≫ i)).IsRepresentedBy jU)
    {H : Fin n → GroupScheme (Spec (CommRingCat.of R))}
    (j : ∀ r, H r ⟶ G)
    (hj : ∀ r, (subgroup i
      (splitTorus.exponentCharacter (Spec (CommRingCat.of R)) I (m r))).IsRepresentedBy (j r))
    (l : ∀ r, H r ⟶ U) (hl : ∀ r, l r ≫ jU = j r)
    (K : Type u) [Field K] [Algebra R K] :
    IsIso (orderedMultiplication
      (fun r => (GroupScheme.baseChange (algebraBaseMap R K)).map (l r))) := by
  let b := algebraBaseMap R K
  let GK := (GroupScheme.baseChange b).obj G
  let iK := splitTorus.baseChangeHom (K := K) G I i
  let νK := splitTorus.exponentCocharacter (Spec (CommRingCat.of K)) I ν
  let aK := fun r => splitTorus.exponentCharacter (Spec (CommRingCat.of K)) I (m r)
  have : Smooth GK.X.hom :=
    inferInstanceAs (Smooth (pullback.snd G.X.hom b))
  have : IsAffineHom GK.X.hom :=
    inferInstanceAs (IsAffineHom (pullback.snd G.X.hom b))
  have hG : GeometricallyConnected G.X.hom := inferInstance
  have : ConnectedSpace GK.X.left :=
    pullback_of_geometrically hG.geometrically_connectedSpace K b
  have hcochar : Dynamic.baseChangeCocharacter b
      (CommGroupScheme.groupHom
        (splitTorus.exponentCocharacter (Spec (CommRingCat.of R)) I ν) ≫ i) =
      CommGroupScheme.groupHom νK ≫ iK := by
    rw [← splitTorus.groupHom_exponentCocharacter_baseChange
      (Spec (CommRingCat.of R)) I b ν]
    change Dynamic.baseChangeCocharacter b _ =
      (Dynamic.baseChangeCocharacter b _ ≫ (splitTorus.baseChangeIso b I).hom) ≫
        ((splitTorus.baseChangeIso b I).inv ≫ (GroupScheme.baseChange b).map i)
    rw [Category.assoc, Iso.hom_inv_id_assoc]
    simp only [Dynamic.baseChangeCocharacter, Functor.map_comp, Category.assoc]
  have hUK : (Dynamic.unipotent (CommGroupScheme.groupHom νK ≫ iK)).IsRepresentedBy
      ((GroupScheme.baseChange b).map jU) := by
    rw [← hcochar, Dynamic.unipotent_baseChange]
    exact hU.baseChange b
  have hjK (r : Fin n) : (subgroup
      (S := splitTorus.commGroupScheme (Spec (CommRingCat.of K)) I) iK (aK r)).IsRepresentedBy
      ((GroupScheme.baseChange b).map (j r)) := by
    dsimp only [iK, aK, splitTorus.baseChangeHom]
    rw [exponentRoot_subgroup_baseChange I i b (m r)]
    exact (hj r).baseChange b
  have haK : Set.range aK = indivisiblePositiveRoots iK νK := by
    simpa only [splitTorus.fieldCharacterEquiv_exponentCharacter,
      splitTorus.fieldCocharacterEquiv_exponentCocharacter] using
      splitTorus.range_fieldCharacterEquiv_indivisiblePositiveRoots
        (k := k) (l := K) I G i
        (splitTorus.exponentCocharacter (Spec (CommRingCat.of k)) I ν) _ ha
  have hinjK : Function.Injective aK := by
    have h := (splitTorus.fieldCharacterEquiv (k := k) (l := K) I).injective.comp hinj
    simpa only [Function.comp_def, splitTorus.fieldCharacterEquiv_exponentCharacter] using h
  have hdisjK : ∀ a ∈ indivisiblePositiveRoots iK νK,
      ∀ c ∈ indivisiblePositiveRoots iK νK, a ≠ c →
        Disjoint (cyclicTail a 1 :
          Set (characterLattice (splitTorus.commGroupScheme (Spec (CommRingCat.of K)) I)))
          (cyclicTail c 1 :
            Set (characterLattice (splitTorus.commGroupScheme (Spec (CommRingCat.of K)) I))) := by
    simpa only [splitTorus.fieldCocharacterEquiv_exponentCocharacter] using
      splitTorus.disjoint_positive_rays_fieldBaseChange (k := k) (l := K) I G i
        (splitTorus.exponentCocharacter (Spec (CommRingCat.of k)) I ν) hdisj
  obtain ⟨e, he⟩ := exists_dynamicRootProductIso_of_representatives
    (k := K) (S := splitTorus.commGroupScheme (Spec (CommRingCat.of K)) I)
    (G := GK) (V := (GroupScheme.baseChange b).obj U)
    (jV := (GroupScheme.baseChange b).map jU)
    (R := fun r => (GroupScheme.baseChange b).obj (H r))
    iK (isSplitTorus_splitTorus I) νK hdisjK aK hinjK haK hUK
    (fun r => (GroupScheme.baseChange b).map (j r)) hjK
  have : Mono ((GroupScheme.baseChange b).map jU).hom.hom := hUK.1
  have hmul : orderedMultiplication
      (fun r => (GroupScheme.baseChange b).map (l r)) = e.hom := by
    apply (cancel_mono ((GroupScheme.baseChange b).map jU).hom.hom).mp
    rw [he, orderedMultiplication_comp]
    congr 1
    funext r
    rw [← Functor.map_comp, hl r]
  rw [hmul]
  infer_instance

private theorem smooth_finProduct {B : Scheme.{u}} {n : ℕ}
    (H : Fin n → GroupScheme B) (hH : ∀ r, Smooth (H r).X.hom) :
    Smooth (∏ᶜ H).X.hom := by
  let e : ULift.{u} (Fin n) ≃ Fin n := Equiv.ulift
  exact smooth_of_over_iso
    ((Grp.forget (Over B)).mapIso (Pi.reindex e H)).symm
    (smooth_pi (H ∘ e) (fun r => hH (e r)))

set_option maxHeartbeats 1600000 in
/-- Over a local ring, smooth integral representatives of the enumerated
root factors multiply isomorphically onto the actual dynamic radical. -/
theorem isIso_orderedRootProduct_localRing
    (hdisj : ∀ a ∈ indivisiblePositiveRoots (splitTorus.baseChangeHom (K := k) G I i)
        (splitTorus.exponentCocharacter (Spec (CommRingCat.of k)) I ν),
      ∀ b ∈ indivisiblePositiveRoots (splitTorus.baseChangeHom (K := k) G I i)
        (splitTorus.exponentCocharacter (Spec (CommRingCat.of k)) I ν), a ≠ b →
        Disjoint (cyclicTail a 1 :
          Set (characterLattice (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I)))
          (cyclicTail b 1 :
            Set (characterLattice (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I))))
    {n : ℕ} (m : Fin n → I → ℤ)
    (hinj : Function.Injective (fun r =>
      splitTorus.exponentCharacter (Spec (CommRingCat.of k)) I (m r)))
    (ha : Set.range (fun r =>
        splitTorus.exponentCharacter (Spec (CommRingCat.of k)) I (m r)) =
      indivisiblePositiveRoots (splitTorus.baseChangeHom (K := k) G I i)
        (splitTorus.exponentCocharacter (Spec (CommRingCat.of k)) I ν))
    {U : GroupScheme (Spec (CommRingCat.of R))} {jU : U ⟶ G}
    (hU : (Dynamic.unipotent
      (CommGroupScheme.groupHom
        (splitTorus.exponentCocharacter (Spec (CommRingCat.of R)) I ν) ≫ i)).IsRepresentedBy jU)
    {H : Fin n → GroupScheme (Spec (CommRingCat.of R))}
    (j : ∀ r, H r ⟶ G)
    (hj : ∀ r, (subgroup i
      (splitTorus.exponentCharacter (Spec (CommRingCat.of R)) I (m r))).IsRepresentedBy (j r))
    (hH : ∀ r, Smooth (H r).X.hom)
    (l : ∀ r, H r ⟶ U) (hl : ∀ r, l r ≫ jU = j r) :
    IsIso (orderedMultiplication l) := by
  have : Smooth U.X.hom := ((dynamicRingSmoothConnected R G _ U jU).1 hU).1
  have : Smooth (∏ᶜ H).X.hom := smooth_finProduct H hH
  apply isIso_of_residueField_fibres (orderedMultiplication l)
  intro s
  let φ := Spec.preimage ((Spec (CommRingCat.of R)).fromSpecResidueField s)
  let : Algebra R ((Spec (CommRingCat.of R)).residueField s) := φ.hom.toAlgebra
  have hb : algebraBaseMap R ((Spec (CommRingCat.of R)).residueField s) =
      (Spec (CommRingCat.of R)).fromSpecResidueField s :=
    Spec.map_preimage _
  have hK := isIso_orderedRootProduct_fieldFibre (k := k) I i ν
    hdisj m hinj ha hU j hj l hl ((Spec (CommRingCat.of R)).residueField s)
  have h : IsIso ((Over.pullback
      (algebraBaseMap R ((Spec (CommRingCat.of R)).residueField s))).map
        (orderedMultiplication l)) := by
    let := hK
    rw [← orderedMultiplication_baseChange]
    infer_instance
  rwa [hb] at h

set_option maxHeartbeats 1600000 in
/-- The original smooth root representatives form an integral product chart,
with the specified ordered multiplication into the ambient group. -/
theorem exists_orderedRootProductIso_localRing
    (hdisj : ∀ a ∈ indivisiblePositiveRoots (splitTorus.baseChangeHom (K := k) G I i)
        (splitTorus.exponentCocharacter (Spec (CommRingCat.of k)) I ν),
      ∀ b ∈ indivisiblePositiveRoots (splitTorus.baseChangeHom (K := k) G I i)
        (splitTorus.exponentCocharacter (Spec (CommRingCat.of k)) I ν), a ≠ b →
        Disjoint (cyclicTail a 1 :
          Set (characterLattice (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I)))
          (cyclicTail b 1 :
            Set (characterLattice (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I))))
    {n : ℕ} (m : Fin n → I → ℤ)
    (hinj : Function.Injective (fun r =>
      splitTorus.exponentCharacter (Spec (CommRingCat.of k)) I (m r)))
    (ha : Set.range (fun r =>
        splitTorus.exponentCharacter (Spec (CommRingCat.of k)) I (m r)) =
      indivisiblePositiveRoots (splitTorus.baseChangeHom (K := k) G I i)
        (splitTorus.exponentCocharacter (Spec (CommRingCat.of k)) I ν))
    {U : GroupScheme (Spec (CommRingCat.of R))} {jU : U ⟶ G}
    (hU : (Dynamic.unipotent
      (CommGroupScheme.groupHom
        (splitTorus.exponentCocharacter (Spec (CommRingCat.of R)) I ν) ≫ i)).IsRepresentedBy jU)
    {H : Fin n → GroupScheme (Spec (CommRingCat.of R))}
    (j : ∀ r, H r ⟶ G)
    (hj : ∀ r, (subgroup i
      (splitTorus.exponentCharacter (Spec (CommRingCat.of R)) I (m r))).IsRepresentedBy (j r))
    (hH : ∀ r, Smooth (H r).X.hom) :
    ∃ e : (∏ᶜ H).X ≅ U.X,
      e.hom ≫ jU.hom.hom = orderedMultiplication j := by
  have hpos (r : Fin n) : 0 < ∑ t, m r t * ν t := by
    have hmem : splitTorus.exponentCharacter (Spec (CommRingCat.of k)) I (m r) ∈
        indivisiblePositiveRoots (splitTorus.baseChangeHom (K := k) G I i)
          (splitTorus.exponentCocharacter (Spec (CommRingCat.of k)) I ν) :=
      ha ▸ Set.mem_range_self r
    simpa only [splitTorus.latticePairing_exponentCharacter_exponentCocharacter]
      using hmem.2
  have hle (r : Fin n) :
      subgroup (S := splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I) i
          (splitTorus.exponentCharacter (Spec (CommRingCat.of R)) I (m r)) ≤
        Dynamic.unipotent (CommGroupScheme.groupHom
          (splitTorus.exponentCocharacter (Spec (CommRingCat.of R)) I ν) ≫ i) :=
    exponentRoot_le_dynamicUnipotent I i (m r) ν (hpos r)
  let l : ∀ r, H r ⟶ U := fun r => (hj r).inclusionHom hU (hle r)
  have hl (r : Fin n) : l r ≫ jU = j r :=
    (hj r).inclusionHom_comp hU (hle r)
  have := isIso_orderedRootProduct_localRing (k := k) I i ν
    hdisj m hinj ha hU j hj hH l hl
  refine ⟨asIso (orderedMultiplication l), ?_⟩
  change orderedMultiplication l ≫ jU.hom.hom = _
  simp only [orderedMultiplication_comp, hl]

section ChosenChart

variable
    (hdisj : ∀ a ∈ indivisiblePositiveRoots (splitTorus.baseChangeHom (K := k) G I i)
        (splitTorus.exponentCocharacter (Spec (CommRingCat.of k)) I ν),
      ∀ b ∈ indivisiblePositiveRoots (splitTorus.baseChangeHom (K := k) G I i)
        (splitTorus.exponentCocharacter (Spec (CommRingCat.of k)) I ν), a ≠ b →
        Disjoint (cyclicTail a 1 :
          Set (characterLattice (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I)))
          (cyclicTail b 1 :
            Set (characterLattice (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I))))
    {n : ℕ} (m : Fin n → I → ℤ)
    (hinj : Function.Injective (fun r =>
      splitTorus.exponentCharacter (Spec (CommRingCat.of k)) I (m r)))
    (ha : Set.range (fun r =>
        splitTorus.exponentCharacter (Spec (CommRingCat.of k)) I (m r)) =
      indivisiblePositiveRoots (splitTorus.baseChangeHom (K := k) G I i)
        (splitTorus.exponentCocharacter (Spec (CommRingCat.of k)) I ν))
    {U : GroupScheme (Spec (CommRingCat.of R))} {jU : U ⟶ G}
    (hU : (Dynamic.unipotent
      (CommGroupScheme.groupHom
        (splitTorus.exponentCocharacter (Spec (CommRingCat.of R)) I ν) ≫ i)).IsRepresentedBy jU)
    {H : Fin n → GroupScheme (Spec (CommRingCat.of R))}
    (j : ∀ r, H r ⟶ G)
    (hj : ∀ r, (subgroup i
      (splitTorus.exponentCharacter (Spec (CommRingCat.of R)) I (m r))).IsRepresentedBy (j r))
    (hH : ∀ r, Smooth (H r).X.hom)

/-- The integral root-product chart on the specified representatives. -/
def orderedRootProductIso_localRing : (∏ᶜ H).X ≅ U.X :=
  Classical.choose (exists_orderedRootProductIso_localRing (k := k) I i ν
    hdisj m hinj ha hU j hj hH)

/-- The chosen integral chart preserves the original ordered multiplication. -/
theorem orderedRootProductIso_localRing_hom_comp :
    (orderedRootProductIso_localRing (k := k) I i ν
      hdisj m hinj ha hU j hj hH).hom ≫ jU.hom.hom = orderedMultiplication j :=
  Classical.choose_spec (exists_orderedRootProductIso_localRing (k := k) I i ν
    hdisj m hinj ha hU j hj hH)

end ChosenChart

end LocalRing

end Langlands.GroupScheme.RelativeRoot
