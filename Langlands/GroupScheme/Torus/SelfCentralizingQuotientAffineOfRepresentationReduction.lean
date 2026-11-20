import Langlands.GroupScheme.Torus.SelfCentralizingQuotientAffineOfRepresentationStatement
import Langlands.GroupScheme.Torus.SelfCentralizingConjugacyClosedEmbeddingStatement
import Langlands.GroupScheme.Torus.RelativeTorusImageFactorizationStatement
import Langlands.GroupScheme.HomScheme.GeneralLinearTorusModuliAffineSumStatement
import Langlands.GroupScheme.Torus.MaximalSelfCentralizing
import Langlands.GroupScheme.Torus.WeylPointTransport
import Langlands.GroupScheme.HomScheme.SmoothTorusSubgroupRepresentabilityProof
import Langlands.GroupScheme.GeneralLinearSmoothProof
import Langlands.GroupScheme.Torus.MultiplicativeTypeExtensionBaseChange
import Langlands.GroupScheme.HomogeneousQuotientBaseChange
import Langlands.GroupScheme.Torus.RelativeFieldComparison
import Mathlib.AlgebraicGeometry.Limits

/-! # Reducing the affine normalizer quotient to three statements -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

namespace SelfCentralizingQuotientAffineReduction

section ConjugacyOrbit

variable {S : Scheme.{u}} {L : GroupScheme S} {M : Over S} {K : GroupScheme M.left}
  {D : GroupScheme S}

/-- **The conjugacy-orbit morphism.** Let `j` be a universal family of closed subtori
of `L`, with parameter scheme `M`, and let `e : D ⟶ L` be a closed torus. An
`X`-valued point `r` of `L` gives the conjugate family `x ↦ r(x) D r(x)⁻¹`, a closed
subtorus of `L_X`. This is the morphism `X ⟶ M` classifying that family. -/
def conjugacyOrbit (j : K ⟶ (GroupScheme.baseChange M.hom).obj L)
    (huni : TorusSubgroupModuli.IsUniversal j) (e : D ⟶ L) (hD : RelativeTorus.IsTorus D)
    (he : IsClosedSubgroup e) {X : Over S} (r : X ⟶ L.X) : X ⟶ M :=
  Classical.choose (huni X (SubgroupFunctor.range (SubgroupFunctor.conjugateFamily e r))
    (TorusSubgroupModuli.isAdmissible_range _
      (SubgroupFunctor.isClosedSubgroup_conjugatePullback X.hom e he _)
      (hD.baseChange X.hom)))

/-- The conjugacy-orbit morphism pulls the universal family back to the conjugate
family. -/
theorem evaluate_conjugacyOrbit (j : K ⟶ (GroupScheme.baseChange M.hom).obj L)
    (huni : TorusSubgroupModuli.IsUniversal j) (e : D ⟶ L) (hD : RelativeTorus.IsTorus D)
    (he : IsClosedSubgroup e) {X : Over S} (r : X ⟶ L.X) :
    TorusSubgroupModuli.evaluate j (conjugacyOrbit j huni e hD he r) =
      SubgroupFunctor.range (SubgroupFunctor.conjugateFamily e r) :=
  (Classical.choose_spec (huni X (SubgroupFunctor.range (SubgroupFunctor.conjugateFamily e r))
    (TorusSubgroupModuli.isAdmissible_range _
      (SubgroupFunctor.isClosedSubgroup_conjugatePullback X.hom e he _)
      (hD.baseChange X.hom)))).1

end ConjugacyOrbit

/-- A quasi-compact scheme with an affine morphism to a scheme that is a disjoint
union of affine opens is affine. -/
theorem isAffine_of_isAffineHom_of_disjointAffineCover {Y M : Scheme.{u}} (φ : Y ⟶ M)
    [IsAffineHom φ] [CompactSpace Y] {J : Type u} (U : J → M.Opens)
    (hU : ∀ k, IsAffineOpen (U k)) (hdisj : Pairwise (Function.onFun Disjoint U))
    (htop : iSup U = ⊤) : IsAffine Y := by
  have hK : IsCompact (Set.range φ.base) := isCompact_range φ.base.hom.continuous
  have hcov : Set.range φ.base ⊆ ⋃ k, (U k : Set M) := by
    intro x _
    have hx : x ∈ (iSup U : M.Opens) := by rw [htop]; trivial
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    exact Set.mem_iUnion.mpr ⟨k, hk⟩
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover (fun k => (U k : Set M))
    (fun k => (U k).isOpen) hcov
  have hV : IsAffineOpen (⨆ k ∈ (s : Set J), U k) :=
    IsAffineOpen.biSup_of_disjoint s.finite_toSet (fun k _ => hU k)
      (fun a _ b _ hab => hdisj hab)
  have hpre : φ ⁻¹ᵁ (⨆ k ∈ (s : Set J), U k) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp (hs ⟨y, rfl⟩)
    obtain ⟨hks, hky⟩ := Set.mem_iUnion.mp hk
    change φ.base y ∈ (⨆ k ∈ (s : Set J), U k : M.Opens)
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨k,
      TopologicalSpace.Opens.mem_iSup.mpr ⟨hks, hky⟩⟩
  have hY := hV.preimage φ
  rw [hpre] at hY
  have : IsAffine (⊤ : Y.Opens) := hY
  exact .of_isIso (Scheme.topIso Y).inv

/-- **The affine-base case.** Over `Spec R`, with a global representation with
central kernel, the three premise statements give affineness of the quotient. -/
theorem isAffineHom_of_spec
    (hGL : TorusSubgroupModuli.GeneralLinearAffineSumStatement.{u})
    (hIm : RelativeTorusImageFactorizationStatement.{u})
    (hCl : SelfCentralizingConjugacyClosedEmbeddingStatement.{u})
    (R : CommRingCat.{u}) (G : GroupScheme (Spec R))
    (hsm : Smooth G.X.hom) (hsep : IsSeparated G.X.hom) (hqc : QuasiCompact G.X.hom)
    (hfib : ∀ s : Spec R,
      ConnectedSpace (RelativeIdentityComponent.residueFiber G s).X.left ∧
        IsAffineHom (RelativeIdentityComponent.residueFiber G s).X.hom)
    (m : ℕ) (ρ : MatrixRepresentation G (Fin m))
    (hρ : ∀ (U : Over (Spec R)) (g h : U ⟶ G.X), g ≫ ρ.hom.hom = 1 → g * h = h * g)
    (T : CommGroupScheme (Spec R)) (t : T.toGrp ⟶ G)
    (hT : RelativeTorus.IsTorus T.toGrp) (ht : IsClosedSubgroup t)
    (hmax : IsFibrewiseMaximalTorus t) (hcent : (torusCentralizer t).IsRepresentedBy t)
    (Y : Over (Spec R)) (p : G.X ⟶ Y)
    (hflat : Flat p.left) (hsurj : Surjective p.left) (hlfp : LocallyOfFinitePresentation p.left)
    (hp : ∀ (U : Over (Spec R)) (g h : U ⟶ G.X),
      g ≫ p = h ≫ p ↔ g⁻¹ * h ∈ (torusNormalizer t).carrier U) :
    IsAffineHom Y.hom := by
  have : Smooth (GeneralLinear.groupScheme (Fin m) R).X.hom :=
    GeneralLinear.smoothStatement (Fin m) R
  have : LocallyOfFinitePresentation (GeneralLinear.groupScheme (Fin m) R).X.hom :=
    inferInstance
  obtain ⟨D, π, e, hD, he, hπf, hπs, hπl, hπe⟩ :=
    hIm (Spec R) T (GeneralLinear.groupScheme (Fin m) R) (t ≫ ρ) hT inferInstance
      inferInstance
  obtain ⟨M, K, j, hj, hK, huni, -⟩ :=
    TorusSubgroupModuli.smoothTorusSubgroupRepresentability (Spec R)
      (GeneralLinear.groupScheme (Fin m) R)
  let f : G.X ⟶ M := conjugacyOrbit j huni e hD he ρ.hom.hom
  have hf := evaluate_conjugacyOrbit j huni e hD he ρ.hom.hom
  obtain ⟨φ, -, hφ⟩ := hCl R G hsm hsep hqc hfib m ρ hρ T t hT ht hmax hcent D π e hD he
    hπf hπs hπl hπe M K j hj hK huni f hf Y p hflat hsurj hlfp hp
  obtain ⟨J, U, hU, hdisj, htop⟩ := hGL R (Fin m) M K j hj hK huni
  have : CompactSpace G.X.left := QuasiCompact.compactSpace_of_compactSpace G.X.hom
  have : CompactSpace Y.left :=
    Function.Surjective.compactSpace p.left.base.hom.continuous hsurj.surj
  have : IsAffine Y.left :=
    isAffine_of_isAffineHom_of_disjointAffineCover φ.left U hU hdisj htop
  infer_instance

/-- **Base change to an affine open.** The hypotheses of the statement, restricted
along an open immersion `i : Spec R ⟶ S` carrying a representation with central
kernel, give affineness of the restricted quotient. -/
theorem isAffineHom_pullback_of_openImmersion
    (hGL : TorusSubgroupModuli.GeneralLinearAffineSumStatement.{u})
    (hIm : RelativeTorusImageFactorizationStatement.{u})
    (hCl : SelfCentralizingConjugacyClosedEmbeddingStatement.{u})
    {S : Scheme.{u}} (G : GroupScheme S)
    [Smooth G.X.hom] [IsSeparated G.X.hom] [QuasiCompact G.X.hom]
    (hfib : ∀ s : S,
      ConnectedSpace (RelativeIdentityComponent.residueFiber G s).X.left ∧
        IsAffineHom (RelativeIdentityComponent.residueFiber G s).X.hom)
    (R : CommRingCat.{u}) (i : Spec R ⟶ S) [IsOpenImmersion i]
    (m : ℕ) (ρ : MatrixRepresentation ((GroupScheme.baseChange i).obj G) (Fin m))
    (hρ : ∀ (U : Over (Spec R)) (g h : U ⟶ ((GroupScheme.baseChange i).obj G).X),
      g ≫ ρ.hom.hom = 1 → g * h = h * g)
    (T : CommGroupScheme S) (t : T.toGrp ⟶ G)
    (hT : RelativeTorus.IsTorus T.toGrp) (ht : IsClosedSubgroup t)
    (hcent : (torusCentralizer t).IsRepresentedBy t)
    (Y : Over S) (p : G.X ⟶ Y)
    (hflat : Flat p.left) (hsurj : Surjective p.left) (hlfp : LocallyOfFinitePresentation p.left)
    (hp : ∀ (U : Over S) (g h : U ⟶ G.X),
      g ≫ p = h ≫ p ↔ g⁻¹ * h ∈ (torusNormalizer t).carrier U) :
    IsAffineHom (pullback.snd Y.hom i) := by
  let GR := (GroupScheme.baseChange i).obj G
  have hsmR : Smooth GR.X.hom := by
    change Smooth (pullback.snd G.X.hom i)
    infer_instance
  have hsepR : IsSeparated GR.X.hom := by
    change IsSeparated (pullback.snd G.X.hom i)
    infer_instance
  have hqcR : QuasiCompact GR.X.hom := by
    change QuasiCompact (pullback.snd G.X.hom i)
    infer_instance
  have hfibR : ∀ s : Spec R,
      ConnectedSpace (RelativeIdentityComponent.residueFiber GR s).X.left ∧
        IsAffineHom (RelativeIdentityComponent.residueFiber GR s).X.hom := by
    intro s
    refine ⟨(ExtensionReduction.connectedSpace_residueFiber_baseChange_iff i G s).mpr
      (hfib (i s)).1, ?_⟩
    let e := ExtensionReduction.residueFiberBaseChangeIso i G s
    have h1 : IsAffineHom ((GroupScheme.baseChange (Spec.map (i.residueFieldMap s))).obj
        (RelativeIdentityComponent.residueFiber G (i s))).X.hom := by
      have := (hfib (i s)).2
      change IsAffineHom (pullback.snd _ (Spec.map (i.residueFieldMap s)))
      infer_instance
    have hiso : IsIso e.inv.hom.hom.left :=
      (inferInstance : IsIso ((Over.forget _).map ((Grp.forget _).map e.inv)))
    rw [← Over.w e.inv.hom.hom]
    infer_instance
  let TR := (CommGroupScheme.baseChange i).obj T
  let tR : TR.toGrp ⟶ GR := (GroupScheme.baseChange i).map t
  have hTR : RelativeTorus.IsTorus TR.toGrp := hT.baseChange i
  have htR : IsClosedSubgroup tR := IsClosedSubgroup.baseChange i ht
  have hcentR : (torusCentralizer tR).IsRepresentedBy tR := by
    have h := hcent.baseChange i
    rwa [← torusCentralizer_baseChange] at h
  have hmaxR : IsFibrewiseMaximalTorus tR := by
    intro s
    apply isMaximalTorus_of_torusCentralizer_eq
      (RelativeTorus.IsTorus.isTorus (k := (Spec R).residueField s) (hTR.baseChange _))
      (IsClosedSubgroup.baseChange _ htR)
    rw [torusCentralizer_baseChange, ← hcentR.2, SubgroupFunctor.range_baseChangeHom]
    rw [SubgroupFunctor.range_baseChangeHom, SubgroupFunctor.range_baseChangeHom]
  let YR := (Over.pullback i).obj Y
  let pR : GR.X ⟶ YR := (Over.pullback i).map p
  have hflatR : Flat pR.left := MorphismProperty.overPullbackMap (P := @Flat) i p hflat
  have hsurjR : Surjective pR.left :=
    MorphismProperty.overPullbackMap (P := @Surjective) i p hsurj
  have hlfpR : LocallyOfFinitePresentation pR.left :=
    MorphismProperty.overPullbackMap (P := @LocallyOfFinitePresentation) i p hlfp
  have hpR : ∀ (U : Over (Spec R)) (g h : U ⟶ GR.X),
      g ≫ pR = h ≫ pR ↔ g⁻¹ * h ∈ (torusNormalizer tR).carrier U := by
    intro U g h
    rw [← ((Over.mapPullbackAdj i).homEquiv U Y).symm.injective.eq_iff,
      (Over.mapPullbackAdj i).homEquiv_naturality_right_symm g p,
      (Over.mapPullbackAdj i).homEquiv_naturality_right_symm h p]
    change baseChangePointsEquiv i G U g ≫ p = baseChangePointsEquiv i G U h ≫ p ↔ _
    rw [hp, mem_torusNormalizer_baseChange_iff, map_mul, map_inv]
  exact isAffineHom_of_spec hGL hIm hCl R GR hsmR hsepR hqcR hfibR m ρ hρ TR tR hTR htR
    hmaxR hcentR YR pR hflatR hsurjR hlfpR hpR

/-- **The reduction.** The three premise statements imply
`SelfCentralizingQuotientAffineOfRepresentationStatement`. -/
theorem selfCentralizingQuotientAffineOfRepresentation_of
    (hGL : TorusSubgroupModuli.GeneralLinearAffineSumStatement.{u})
    (hIm : RelativeTorusImageFactorizationStatement.{u})
    (hCl : SelfCentralizingConjugacyClosedEmbeddingStatement.{u}) :
    SelfCentralizingQuotientAffineOfRepresentationStatement.{u} := by
  intro S G hsm hsep hqc hfib hrep T t hT ht _ hcent Y p hflat hsurj hlfp hp
  have : Smooth G.X.hom := hsm
  have : IsSeparated G.X.hom := hsep
  have : QuasiCompact G.X.hom := hqc
  choose R i hi hs m ρ hρ using hrep
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (fun s => (i s).opensRange) ?_ fun s => ?_
  · rw [eq_top_iff]
    intro x _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hs x⟩
  · have := hi s
    exact (MorphismProperty.arrow_mk_iso_iff _ (morphismRestrictOpensRange Y.hom (i s))).mpr
      (isAffineHom_pullback_of_openImmersion hGL hIm hCl G hfib (R s) (i s) (m s) (ρ s) (hρ s)
        T t hT ht hcent Y p hflat hsurj hlfp hp)

end SelfCentralizingQuotientAffineReduction

end Langlands.GroupScheme
