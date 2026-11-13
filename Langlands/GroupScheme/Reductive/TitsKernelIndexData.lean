import Langlands.GroupScheme.Reductive.TitsKernelTorus
import Langlands.GroupScheme.Reductive.TitsKernelRootComparison
import Langlands.GroupScheme.Torus.FiniteGaloisSplittingProof
import Langlands.GroupScheme.Rational.SplitCentralEmbedding
import Langlands.GroupScheme.Absolute.CocharacterAveraging
import Langlands.GroupScheme.Torus.LatticeBaseInvariants
import Langlands.GroupScheme.Torus.WeilRestrictionNormOneCharacters
import Langlands.LinearAlgebra.RootDatumZeroFace
import Langlands.GroupScheme.Torus.ExistenceProof

/-! # Index data of the semisimple anisotropic kernel -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]

local notation "E" => SeparableClosure k
local notation "bE" => algebraBaseMap k (SeparableClosure k)
local notation "BG" => GroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))
local notation "BC" => CommGroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))

local instance kernelBaseChangeAffine {X : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom X.X.hom] : IsAffineHom ((BG).obj X).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd X.X.hom bE)
  infer_instance

local instance kernelBaseChangeFiniteType {X : GroupScheme (Spec (CommRingCat.of k))}
    [LocallyOfFiniteType X.X.hom] : LocallyOfFiniteType ((BG).obj X).X.hom := by
  change LocallyOfFiniteType (CategoryTheory.Limits.pullback.snd X.X.hom bE)
  infer_instance

/-- Every torus over `k` splits over the separable closure. -/
theorem isSplitTorus_baseChange_separableClosure {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (hT : IsTorus T.toGrp) : IsSplitTorus ((BC).obj T).toGrp :=
  SplittingAssembly.isSplit_of_isSepClosed_of_prerequisites
    Langlands.CoalgebraDescent.separablyClosedGroupLikeSpanning _
    (IsTorus.baseChange_of_isAlgebraic k (SeparableClosure k) T.toGrp hT)

namespace TitsIndexData

variable {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (d : TitsIndexData G) {M : GroupScheme (Spec (CommRingCat.of k))} {j : M ⟶ G}
  (hj : (torusCentralizer d.splitInclusion).IsRepresentedBy j)
  {D : GroupScheme (Spec (CommRingCat.of k))} {i : D ⟶ M} [Mono i.hom.hom]

/-- Over the separable closure, the roots of any root datum of `(D, T ∩ D)` are
the restrictions of the roots of `d` vanishing on the maximal split torus, with
the matching coroots. -/
theorem exists_kernelRootEquiv (hi : IsDerivedSubgroup i)
    [IsAffineHom D.X.hom] [LocallyOfFiniteType D.X.hom]
    {K : Type u}
    {Q : RootDatum K (characterLattice ((BC).obj (d.kernelTorus hj (i := i))))
      (cocharacterLattice ((BC).obj (d.kernelTorus hj (i := i))))}
    (hQ : IsRootDatumOf (T := (BC).obj (d.kernelTorus hj (i := i)))
      ((BG).map (d.kernelInclusion hj)) Q) :
    ∃ φ : K ≃ {p : d.pinning.rootIndex //
        (BC).map d.torusMap ≫ d.pinning.rootDatum.root p = 0}, ∀ q,
      Q.root q = (BC).map (d.kernelTorusMap hj) ≫ d.pinning.rootDatum.root (φ q) ∧
      Q.coroot q ≫ (BC).map (d.kernelTorusMap hj) = d.pinning.rootDatum.coroot (φ q) := by
  have hM := d.centralizer_isConnectedReductive hj
  have : Smooth M.X.hom := hM.smooth
  have : IsAffineHom M.X.hom := hM.isAffineHom
  have hME : IsConnectedReductive ((BG).obj M) :=
    connectedReductiveFieldExtensionStatement k E M hM
  have hDs := d.kernel_isSemisimple hj hi
  have : Smooth D.X.hom := hDs.isConnectedReductive.smooth
  have hS := d.maximalSplit.1.1
  have htM := d.isMaximalTorus_centralizerTorus hj
  have htMmax : IsMaximalTorus (T := (BC).obj d.pinning.torus)
      ((BG).map (d.centralizerTorus hj)) :=
    (maximalTorusBaseChange k E M _ _ htM.1 htM.2.1).mp htM
  have htD := d.isMaximalTorus_kernelInclusion hj hi
  have htDmax : IsMaximalTorus (T := (BC).obj (d.kernelTorus hj (i := i)))
      ((BG).map (d.kernelInclusion hj)) :=
    (maximalTorusBaseChange k E D _ _ htD.1 htD.2.1).mp htD
  have hTDE : IsSplitTorus ((BC).obj (d.kernelTorus hj (i := i))).toGrp :=
    isSplitTorus_baseChange_separableClosure htD.1
  have hiE : IsDerivedSubgroup ((BG).map i) :=
    hi.baseChange_of_eq bE (derivedSubgroup_baseChange_eq_of_field bE M)
  have hjE : (torusCentralizer (T := (BC).obj d.splitTorus)
      ((BG).map d.splitInclusion)).IsRepresentedBy ((BG).map j) := by
    rw [torusCentralizer_baseChange]
    exact hj.baseChange bE
  exact exists_derivedCentralizerRootEquiv (T := (BC).obj d.pinning.torus)
    (A := (BC).obj d.splitTorus) (TD := (BC).obj (d.kernelTorus hj (i := i)))
    ((BG).map d.splitInclusion) (hS.baseChange bE) ((BG).map j) hjE hME
    ((BG).map d.pinning.inclusion) d.pinning.isSplitTorus d.pinning.isRootDatum
    ((BG).map (d.centralizerTorus hj))
    (by rw [← Functor.map_comp, d.centralizerTorus_comp hj]) htMmax
    ((BC).map d.torusMap) (by rw [← d.square, Functor.map_comp]; rfl)
    ((BG).map i) hiE ((BG).map (d.kernelInclusion hj)) hTDE htDmax
    ((BC).map (d.kernelTorusMap hj))
    (by rw [← Functor.map_comp, d.kernelInclusion_comp hj, Functor.map_comp]; rfl) hQ

end TitsIndexData

/-- Precomposition on actual integral character lattices. -/
def characterPrecompInt {S : Scheme.{u}} {A B : CommGroupScheme S} (f : A ⟶ B) :
    characterLattice B →ₗ[ℤ] characterLattice A :=
  AddMonoidHom.toIntLinearMap
    { toFun := fun χ => f ≫ χ
      map_zero' := by simp
      map_add' := fun χ ψ => Preadditive.comp_add _ _ _ _ _ _ }

@[simp] theorem characterPrecompInt_apply {S : Scheme.{u}} {A B : CommGroupScheme S}
    (f : A ⟶ B) (χ : characterLattice B) : characterPrecompInt f χ = f ≫ χ := rfl

/-- Character restriction and cocharacter pushforward are adjoint for the actual
lattice pairings. -/
theorem latticePairing_precomp {A B : CommGroupScheme (Spec (CommRingCat.of k))}
    (f : A ⟶ B) (χ : characterLattice B) (ν : cocharacterLattice A) :
    latticePairing A (f ≫ χ) ν = latticePairing B χ (ν ≫ f) := by
  rw [latticePairing_apply, latticePairing_apply, Category.assoc]

namespace TitsIndexData

variable {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G)

/-- The positive cocharacter of the maximal split torus, pushed into the maximal
torus and base changed to the separable closure. -/
def kernelCoweight : cocharacterLattice ((BC).obj d.pinning.torus) :=
  cocharacterLattice.baseChange bE d.pinning.torus (d.positiveCocharacter ≫ d.torusMap)

/-- The value of an absolute root on the coweight is the pairing of its actual
restriction with the positive cocharacter. -/
theorem root'_kernelCoweight (a : d.pinning.rootIndex) :
    d.pinning.rootDatum.root' a d.kernelCoweight =
      latticePairing d.splitTorus (d.rootRestriction a) d.positiveCocharacter := by
  change d.pinning.rootDatum.toLinearMap (d.pinning.rootDatum.root a) d.kernelCoweight = _
  rw [d.pinning.isRootDatum.1, kernelCoweight, cocharacterLattice.baseChange_comp,
    ← latticePairing_precomp,
    ← latticePairing_baseChange bE d.splitTorus (d.rootRestriction a) d.positiveCocharacter]
  have hx : characterLattice.baseChange bE d.splitTorus (d.rootRestriction a) =
      (BC).map d.torusMap ≫ d.pinning.rootDatum.root a :=
    (characterLattice.baseChangeEquiv bE d.splitTorus d.maximalSplit.1.1).apply_symm_apply _
  rw [hx]

/-- Zero restriction is zero restriction after base change. -/
theorem rootRestriction_eq_zero_iff (a : d.pinning.rootIndex) :
    d.rootRestriction a = 0 ↔ (BC).map d.torusMap ≫ d.pinning.rootDatum.root a = 0 :=
  (characterLattice.baseChangeEquiv bE d.splitTorus d.maximalSplit.1.1).symm.map_eq_zero_iff

theorem rootRestriction_neg (a : d.pinning.rootIndex) :
    letI := d.pinning.rootDatum.indexNeg
    d.rootRestriction (-a) = -d.rootRestriction a := by
  let := d.pinning.rootDatum.indexNeg
  have h : d.pinning.rootDatum.root (-a) = -d.pinning.rootDatum.root a := by
    change d.pinning.rootDatum.root (d.pinning.rootDatum.reflectionPerm a a) = _
    rw [d.pinning.rootDatum.root_reflectionPerm, d.pinning.rootDatum.reflection_apply_self]
  change (characterLattice.baseChangeEquiv bE d.splitTorus d.maximalSplit.1.1).symm
      ((BC).map d.torusMap ≫ d.pinning.rootDatum.root (-a)) =
    -(characterLattice.baseChangeEquiv bE d.splitTorus d.maximalSplit.1.1).symm
      ((BC).map d.torusMap ≫ d.pinning.rootDatum.root a)
  rw [h, Preadditive.comp_neg, map_neg]

/-- An absolute root has zero restriction exactly when it vanishes on the coweight. -/
theorem rootRestriction_eq_zero_iff_root' (a : d.pinning.rootIndex) :
    d.rootRestriction a = 0 ↔ d.pinning.rootDatum.root' a d.kernelCoweight = 0 := by
  constructor
  · intro h
    rw [root'_kernelCoweight, h, map_zero, LinearMap.zero_apply]
  · intro h
    by_contra hne
    let := d.pinning.rootDatum.indexNeg
    rw [root'_kernelCoweight] at h
    have h1 : d.pinning.base.IsPos a ↔
        0 < latticePairing d.splitTorus (d.rootRestriction a) d.positiveCocharacter :=
      d.compatible a hne
    have hne' : d.rootRestriction (-a) ≠ 0 := by
      rw [rootRestriction_neg]
      exact neg_ne_zero.mpr hne
    have h2 : d.pinning.base.IsPos (-a) ↔
        0 < latticePairing d.splitTorus (d.rootRestriction (-a)) d.positiveCocharacter :=
      d.compatible (-a) hne'
    rw [h] at h1
    rw [rootRestriction_neg, map_neg, LinearMap.neg_apply, h, neg_zero] at h2
    rcases RootPairing.Base.IsPos.or_neg d.pinning.base a with hp | hp
    · exact lt_irrefl 0 (h1.mp hp)
    · exact lt_irrefl 0 (h2.mp hp)

/-- The positivity compatibility of `d`, in terms of the base-changed coweight. -/
theorem sign_kernelCoweight (a : d.pinning.rootIndex)
    (h : d.pinning.rootDatum.root' a d.kernelCoweight ≠ 0) :
    d.pinning.base.IsPos a ↔ 0 < d.pinning.rootDatum.root' a d.kernelCoweight := by
  have hne : d.rootRestriction a ≠ 0 := fun h0 => h ((d.rootRestriction_eq_zero_iff_root' a).mp h0)
  rw [root'_kernelCoweight]
  exact d.compatible a hne

/-- The base-changed coweight is fixed by the Galois action. -/
theorem galoisRepresentation_kernelCoweight (σ : E ≃ₐ[k] E) :
    cocharacterLattice.galoisRepresentation k E d.pinning.torus σ d.kernelCoweight =
      d.kernelCoweight :=
  cocharacterLattice.galoisRepresentation_baseChange k E d.pinning.torus σ _

/-- The ordinary Galois action preserves values on the coweight. -/
theorem root'_galoisAction (σ : E ≃ₐ[k] E) (a : d.pinning.rootIndex) :
    d.pinning.rootDatum.root' ((d.pinning.galoisAction σ).indexEquiv a) d.kernelCoweight =
      d.pinning.rootDatum.root' a d.kernelCoweight := by
  change d.pinning.rootDatum.toLinearMap (d.pinning.rootDatum.root
      (IsRootDatumOf.galoisRootIndexEquiv k E d.pinning.inclusion d.pinning.isRootDatum σ a))
      d.kernelCoweight = d.pinning.rootDatum.toLinearMap (d.pinning.rootDatum.root a)
      d.kernelCoweight
  rw [d.pinning.isRootDatum.1, IsRootDatumOf.galoisRootIndexEquiv_root]
  conv_lhs => rw [← d.galoisRepresentation_kernelCoweight σ]
  exact latticePairing_galoisRepresentation k E d.pinning.torus σ _ _


end TitsIndexData

open Langlands.LinearAlgebra.RootDatumZeroFace in
/-- **Tits §§2.2–2.3, reduction.** If every actual derived subgroup of the
centralizer of the maximal split torus is semisimple and anisotropic, then it
has actual index data whose index is the subdiagram of `d` on `Δ₀`. -/
theorem titsAnisotropicKernelIndex_of_anisotropicKernel
    (hA : TitsAnisotropicKernelStatement.{u}) : TitsAnisotropicKernelIndexStatement.{u} := by
  intro k _ G _ _ d M j hj D i hi
  have hDs : IsSemisimple D := d.kernel_isSemisimple hj hi
  have hDan : IsAnisotropic D := (hA k G d M j hj D i hi).2
  have : IsAffineHom D.X.hom := hDs.isConnectedReductive.isAffineHom
  have : Smooth D.X.hom := hDs.isConnectedReductive.smooth
  have : IsClosedImmersion i.hom.hom.left := hi.1
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  refine ⟨inferInstance, inferInstance, ?_⟩
  have htD := d.isMaximalTorus_kernelInclusion hj hi
  have hDE : IsConnectedReductive ((GroupScheme.baseChange
      (algebraBaseMap k (SeparableClosure k))).obj D) :=
    connectedReductiveFieldExtensionStatement k (SeparableClosure k) D hDs.isConnectedReductive
  have hTDE : IsSplitTorus ((CommGroupScheme.baseChange
      (algebraBaseMap k (SeparableClosure k))).obj (d.kernelTorus hj (i := i))).toGrp :=
    isSplitTorus_baseChange_separableClosure htD.1
  have htDE : IsMaximalTorus (T := (CommGroupScheme.baseChange
      (algebraBaseMap k (SeparableClosure k))).obj (d.kernelTorus hj (i := i)))
      ((GroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).map
        (d.kernelInclusion hj)) :=
    (maximalTorusBaseChange k (SeparableClosure k) D _ _ htD.1 htD.2.1).mp htD
  obtain ⟨K, _, Q, hQ, hQred⟩ := rootDatumExistence (SeparableClosure k)
    ((GroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).obj D) hDE
    ((CommGroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).obj
      (d.kernelTorus hj (i := i))) hTDE _ htDE
  obtain ⟨φ₀, hφ₀⟩ := d.exists_kernelRootEquiv hj hi hQ
  have hτmono : Mono (CommGroupScheme.groupHom ((CommGroupScheme.baseChange
      (algebraBaseMap k (SeparableClosure k))).map (d.kernelTorusMap hj (i := i)))).hom.hom.left :=
    ((d.isClosedSubgroup_kernelTorusMap hj hi).baseChange
      (algebraBaseMap k (SeparableClosure k))).mono
  let F : FaceDatum d.pinning.rootDatum d.pinning.base d.kernelCoweight Q :=
    { sign := d.sign_kernelCoweight
      weightMap := characterPrecompInt ((CommGroupScheme.baseChange
        (algebraBaseMap k (SeparableClosure k))).map (d.kernelTorusMap hj (i := i)))
      coweightMap := RealTorusSpace.cocharacterMapInt ((CommGroupScheme.baseChange
        (algebraBaseMap k (SeparableClosure k))).map (d.kernelTorusMap hj (i := i)))
      coweightMap_injective := RealTorusSpace.cocharacterMapInt_injective _
      pairing_comm := fun x y => by
        rw [hQ.1, d.pinning.isRootDatum.1]
        exact latticePairing_precomp _ _ _
      indexEquiv := φ₀.trans (Equiv.subtypeEquivRight fun p =>
        (d.rootRestriction_eq_zero_iff p).symm.trans (d.rootRestriction_eq_zero_iff_root' p))
      root_eq := fun q => (hφ₀ q).1
      coroot_eq := fun q => (hφ₀ q).2 }
  let pin : GaloisPinningData k (SeparableClosure k) D :=
    { torus := d.kernelTorus hj (i := i)
      inclusion := d.kernelInclusion hj
      isConnectedReductive := hDE
      isSplitTorus := hTDE
      isMaximalTorus := htDE
      rootIndex := K
      rootDatum := Q
      isRootDatum := hQ
      isReduced := hQred
      base := F.base
      pinning := RootPinning.ofSplitMaximalTorus hDE hTDE _ htDE Q hQ F.base }
  have hmaxsplit : IsMaximalSplitTorus (TorusExistence.trivialTorusHom D) := by
    refine ⟨⟨isSplitTorus_splitTorus _, TorusExistence.isClosedSubgroup_trivialTorusHom D⟩, ?_⟩
    intro T' i' hi' f hf
    have := hDan.subsingleton_hom_of_isSplitSubtorus hi' T'.toGrp
    have := splitTorus.subsingleton_hom_of_isEmpty (S := Spec (CommRingCat.of k))
      PEmpty.{u + 1} (TorusExistence.trivialTorus k).toGrp
    let g : T'.toGrp ⟶ (TorusExistence.trivialTorus k).toGrp :=
      default ≫ TorusExistence.splitTorusEmptyIso.inv
    exact ⟨g, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  have hchar : Subsingleton (characterLattice (TorusExistence.trivialTorus k)) := by
    have := splitTorus.subsingleton_hom_of_isEmpty (S := Spec (CommRingCat.of k))
      PEmpty.{u + 1} (Gm (Spec (CommRingCat.of k))).toGrp
    exact ⟨fun f g => congrArg Additive.ofMul (Subsingleton.elim f.toMul g.toMul)⟩
  have hsq : Subsingleton ((TorusExistence.trivialTorus k).toGrp ⟶ D) :=
    splitTorus.subsingleton_hom_of_isEmpty (S := Spec (CommRingCat.of k)) PEmpty.{u + 1} D
  let e : TitsIndexData D :=
    { isSemisimple := hDs
      pinning := pin
      maximalTorus := htD
      splitTorus := TorusExistence.trivialTorus k
      splitInclusion := TorusExistence.trivialTorusHom D
      maximalSplit := hmaxsplit
      torusMap := 0
      square := Subsingleton.elim _ _
      positiveCocharacter := 0
      generic := by
        intro α hα
        rw [hDan.relativeRoots_eq_empty hmaxsplit.1] at hα
        exact absurd hα (Set.notMem_empty α)
      compatible := fun a ha => absurd (Subsingleton.elim _ _) ha }
  let φ : K ≃ {a : d.pinning.rootIndex // d.rootRestriction a = 0} :=
    φ₀.trans (Equiv.subtypeEquivRight fun p => (d.rootRestriction_eq_zero_iff p).symm)
  have hφF (q : K) : (φ q : d.pinning.rootIndex) = F.indexEquiv q := rfl
  refine ⟨e, d.kernelTorusMap hj, φ, d.kernelTorusMap_comp_inclusion hj,
    fun q => (hφ₀ q).1, fun q => (hφ₀ q).2, fun q r => F.pairing_eq q r,
    fun q => F.mem_base_support q, ?_⟩
  intro σ q _
  let gal : RootPairing.Aut d.pinning.rootDatum := d.pinning.galoisAction σ
  let gal' : RootPairing.Aut Q := pin.galoisAction σ
  obtain ⟨w'₀, hw'₀⟩ := pin.exists_weyl_mul_galoisAction_eq_starAction σ
  let w' : RootPairing.Aut Q := w'₀.val
  have hw'mem : w' ∈ Q.weylGroup := w'₀.property
  let star' : RootPairing.Aut Q := (pin.starAction σ).val
  have hw' : w' * gal' = star' := hw'₀
  have hb' : ∀ r, r ∈ F.base.support ↔ (w' * gal').indexEquiv r ∈ F.base.support := by
    rw [hw']
    exact (pin.starAction σ).property
  have hδν : ∀ a, d.pinning.rootDatum.root' (gal.indexEquiv a) d.kernelCoweight =
      d.pinning.rootDatum.root' a d.kernelCoweight := d.root'_galoisAction σ
  have hδφ : ∀ r, gal.indexEquiv (F.indexEquiv r).val =
      (F.indexEquiv (gal'.indexEquiv r)).val := by
    intro r
    have h1 : d.pinning.rootDatum.root (gal.indexEquiv (F.indexEquiv r).val) =
        characterLattice.galoisRepresentation k (SeparableClosure k) d.pinning.torus σ
          (d.pinning.rootDatum.root (F.indexEquiv r)) :=
      IsRootDatumOf.galoisRootIndexEquiv_root k (SeparableClosure k) d.pinning.inclusion
        d.pinning.isRootDatum σ _
    have h2 : Q.root (gal'.indexEquiv r) =
        characterLattice.galoisRepresentation k (SeparableClosure k)
          (d.kernelTorus hj (i := i)) σ (Q.root r) :=
      IsRootDatumOf.galoisRootIndexEquiv_root k (SeparableClosure k) (d.kernelInclusion hj)
        hQ σ r
    have hz : d.pinning.rootDatum.root' (gal.indexEquiv (F.indexEquiv r).val)
        d.kernelCoweight = 0 := by
      rw [hδν]
      exact F.root'_index r
    obtain ⟨m, hm⟩ := F.exists_index hz
    have h3 : Q.root m = Q.root (gal'.indexEquiv r) := by
      rw [F.root_eq m, hm, h2, F.root_eq r]
      change _ ≫ _ = characterLattice.galoisRepresentation k (SeparableClosure k) _ σ (_ ≫ _)
      rw [h1, characterLattice.galoisRepresentation_precompose]
    have hm' : m = gal'.indexEquiv r := Q.root.injective h3
    rw [← hm, hm']
  obtain ⟨w, hw, hbased, hφw⟩ :=
    F.exists_based_correction gal gal' hδν hδφ hw'mem hb'
  have hstar : (⟨w * gal, hbased⟩ : d.pinning.toSplitPinning.basedRootDatumAut) =
      d.pinning.starAction σ := by
    apply d.pinning.toSplitPinning.basedRootDatum_representative_unique gal
    · change w * gal * gal⁻¹ ∈ d.pinning.rootDatum.weylGroup
      rw [mul_inv_cancel_right]
      exact hw
    · exact d.pinning.starAction_mul_galoisAction_inv_mem σ
  have key := hφw q
  rw [hw'] at key
  calc (φ ((e.pinning.starAction σ).val.indexEquiv q) : d.pinning.rootIndex)
      = (F.indexEquiv (star'.indexEquiv q)).val := rfl
    _ = (w * gal).indexEquiv (F.indexEquiv q).val := key.symm
    _ = (d.pinning.starAction σ).val.indexEquiv (F.indexEquiv q).val :=
      congrArg (fun θ : d.pinning.toSplitPinning.basedRootDatumAut =>
        θ.val.indexEquiv (F.indexEquiv q).val) hstar
    _ = _ := rfl

end Langlands.GroupScheme
