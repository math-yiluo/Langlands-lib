import Langlands.GroupScheme.SimplyConnected.RankOneLeviDerivedGenerationReduction
import Langlands.GroupScheme.Rational.StandardCocharacterProof
import Langlands.GroupScheme.Rational.StandardLeviAnnihilator
import Langlands.GroupScheme.Rational.RelativeSimpleRootBasisProof
import Langlands.GroupScheme.Rational.TorusCentralizerImage
import Langlands.GroupScheme.Rational.LeviFactorization
import Langlands.GroupScheme.Rational.SplitRankTransport
import Langlands.GroupScheme.Reductive.NormalIsogenyComplementProof
import Langlands.GroupScheme.Reductive.AlmostSimpleNormalSubgroup
import Langlands.GroupScheme.Derived.AlmostSimplePerfect
import Langlands.GroupScheme.Derived.SemisimplePerfectProof
import Langlands.GroupScheme.Derived.SemisimpleProof
import Langlands.GroupScheme.Derived.KernelAnnihilation
import Langlands.GroupScheme.CommutingFactorRetraction

/-!
# The rank-one Levi factor dichotomy

This module proves `RankOneLeviFactorDichotomyStatement` through the simply connected derived
group of the standard Levi subgroup of a simple relative root and its normal complement to the
rank-one Levi factor.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- In a simply connected group, every closed normal almost-simple subgroup of the derived
subgroup of the minimal Levi either lies in a given rank-one Levi factor or commutes with it. -/
theorem rankOneLeviFactorDichotomy : RankOneLeviFactorDichotomyStatement.{u} := by
  intro k _ G _ hsc S i hi ν hν M j hj α hα A a ha D d hd B b hB hbc hbn
  have hGred := hsc.isSemisimple.isConnectedReductive
  have : Smooth G.X.hom := hGred.smooth
  have : ConnectedSpace G.X.left := hGred.connectedSpace
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : Mono i.hom.hom.left := hi.isSplitSubtorus.mono
  have hT : IsSplitTorus S.toGrp := hi.isSplitSubtorus.1
  obtain ⟨hac, hAsc, hA, hsr, hroot, hcen, hnorm⟩ := ha
  -- the Levi subgroup `L = Z_G(ζ)` for a standard cocharacter `ζ` of `{α}`
  have hJ : ({α} : Set (characterLattice S)) ⊆ simpleRelativeRoots i ν :=
    Set.singleton_subset_iff.2 hα
  obtain ⟨⟨ζ, hζ⟩, hcmp⟩ := standardCocharacter k G hGred S i hi ν hν {α} hJ
  have hfin : (simpleRelativeRoots i ν).Finite :=
    Set.finite_coe_iff.mp (relativeSimpleRootBasis k G hGred S i hi ν hν).1
  have hLeq : Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ i) =
      cocharacterAnnihilatorCentralizer i {α} := by
    rw [← (hcmp ζ hζ).2.1]
    exact standardLevi_eq_cocharacterAnnihilatorCentralizer i ν hfin {α} ⟨ζ, hζ⟩
  have hLsub : ∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ G.X),
      g ∈ (Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ i)).carrier T →
      ∀ ζ' : cocharacterLattice S, latticePairing S α ζ' = 0 →
        g ∈ (Dynamic.centralizer (CommGroupScheme.groupHom ζ' ≫ i)).carrier T := by
    intro T g hg ζ' hζ'
    rw [hLeq, mem_cocharacterAnnihilatorCentralizer] at hg
    exact hg ζ' (by simpa using hζ')
  let χ := CommGroupScheme.groupHom ζ ≫ i
  let L := Dynamic.Affine.centralizerScheme χ
  let l : L ⟶ G := Dynamic.Affine.centralizerHom χ
  have hl : (Dynamic.centralizer χ).IsRepresentedBy l :=
    Dynamic.Affine.isRepresentedBy_centralizerHom χ
  have hlc : IsClosedSubgroup l := Dynamic.Affine.isClosedSubgroup_centralizerHom χ
  have hLred : IsConnectedReductive L := dynamicCentralizerReductive k G hGred χ L l hlc hl
  have : IsAffineHom L.X.hom := hLred.isAffineHom
  have : Smooth L.X.hom := hLred.smooth
  obtain ⟨Gα, dα, -, -, hdα⟩ := derivedSubgroupRepresentability k L
  have hGαss : IsSemisimple Gα := derivedSubgroupSemisimple k L Gα dα hLred hdα
  -- the derived subgroup of `L` is simply connected
  let dfac := (isSplitTorus_gm (S := Spec (CommRingCat.of k))).dominantFactorization χ
  have hlT : (torusCentralizer dfac.inclusion).IsRepresentedBy l := by
    rw [← dynamicCentralizer_eq_torusCentralizer_image χ dfac]
    exact hl
  have hGαsc : IsSimplyConnected Gα :=
    splitTorusCentralizerDerivedSimplyConnected k G hsc dfac.image dfac.inclusion
      dfac.isSplitSubtorus L l hlT Gα dα hdα
  -- `A` lies in `L` and, being perfect, in the derived subgroup `Gα` of `L`
  have haL : SubgroupFunctor.range a ≤ Dynamic.centralizer χ :=
    hcen ζ (hζ.2.1 α (Set.mem_singleton α))
  let aL : A ⟶ L := SubgroupFunctor.IsRepresentedBy.factorHom hl a haL
  have haL_comp : aL ≫ l = a := SubgroupFunctor.IsRepresentedBy.factorHom_comp hl a haL
  have hAtop : derivedSubgroup A = ⊤ := hA.derivedSubgroup_eq_top
  have haGα : SubgroupFunctor.range aL ≤ SubgroupFunctor.range dα := by
    intro T g hg
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.1 hg
    rw [hdα.2]
    apply mem_derivedSubgroup_comp aL
    rw [hAtop]
    trivial
  have hdαrep : (SubgroupFunctor.range dα).IsRepresentedBy dα := ⟨hdα.1.mono_hom, rfl⟩
  let aG : A ⟶ Gα := SubgroupFunctor.IsRepresentedBy.factorHom hdαrep aL haGα
  have haG_comp : aG ≫ dα = aL :=
    SubgroupFunctor.IsRepresentedBy.factorHom_comp hdαrep aL haGα
  let lG : Gα ⟶ G := dα ≫ l
  have hlG : aG ≫ lG = a := by
    rw [← Category.assoc, haG_comp, haL_comp]
  have hlGc : IsClosedSubgroup lG := hdα.1.comp hlc
  have : Mono lG.hom.hom := hlGc.mono_hom
  have hlGrep : (SubgroupFunctor.range lG).IsRepresentedBy lG := ⟨hlGc.mono_hom, rfl⟩
  have haGc : IsClosedSubgroup aG := IsClosedSubgroup.of_comp hlGc (by rw [hlG]; exact hac)
  have hpointL : ∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ Gα.X),
      g ≫ lG.hom.hom ∈ (Dynamic.centralizer χ).carrier T := by
    intro T g
    rw [← hl.2]
    exact SubgroupFunctor.mem_range.2 ⟨g ≫ dα.hom.hom, by
      simp only [lG, Grp.comp_hom_hom, Category.assoc]⟩
  have hconj : ∀ {T : Over (Spec (CommRingCat.of k))} {X Y : GroupScheme (Spec (CommRingCat.of k))}
      (f : X ⟶ Y) (g x : T ⟶ X.X),
      (g * x * g⁻¹) ≫ f.hom.hom = (g ≫ f.hom.hom) * (x ≫ f.hom.hom) * (g ≫ f.hom.hom)⁻¹ := by
    intro T X Y f g x
    simp only [MonObj.mul_comp, GrpObj.inv_comp]
  -- `A` is normal in `Gα`
  have haGn : (SubgroupFunctor.range aG).IsNormal := by
    intro T g x _ hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.1 hx
    have hmem := hnorm T (g ≫ lG.hom.hom) (y ≫ a.hom.hom)
      (fun ζ' hζ' => hLsub T _ (hpointL T g) ζ' hζ') ⟨y, rfl⟩
    obtain ⟨y', hy'⟩ := SubgroupFunctor.mem_range.1 hmem
    refine SubgroupFunctor.mem_range.2 ⟨y', ?_⟩
    apply (cancel_mono lG.hom.hom).1
    rw [hconj, Category.assoc, ← Grp.comp_hom_hom, hlG, hy', ← hlG]
    simp only [lG, Grp.comp_hom_hom, Category.assoc]
  -- a normal complement `K` of `A` in the simply connected `Gα`
  have hAred := hA.isSemisimple.isConnectedReductive
  obtain ⟨-, K, κ, hKss, hκc, hκn, hAKss, hc, hiso⟩ :=
    semisimpleNormalIsogenyComplement k Gα A hGαss aG haGc hAred.smooth hAred.connectedSpace haGn
  have : IsIso (commutingSubgroupMultiplicationHom aG κ hc) :=
    hGαsc.central_isogeny_isIso (A ⊗ K) _ hAKss hiso
  -- a rational reflection representative `n` for `α` lying in `A`
  have hfac : RelativeRoot.HasRankOneFactorization i := rootRankOneFactorization k G hGred S i hi
  have hαroot : α ∈ relativeRoots i := hα.1.1
  have hneg : RelativeRoot.subgroup i (-α) ≤ SubgroupFunctor.range a :=
    IsRankOneLeviFactor.subgroup_neg_le_range hT hfac hαroot
      ⟨hac, hAsc, hA, hsr, hroot, hcen, hnorm⟩
  obtain ⟨x, hx, hx1⟩ := RelativeRoot.exists_rootPoint_actual hT i hαroot
  obtain ⟨⟨p, hp, -⟩, -⟩ := hfac α hαroot x hx hx1
  let n : normalizerPoints i := ⟨p.1 * x * p.2, hp.2.2⟩
  have hnα : weylAction i n α = -α := hp.weylAction_eq_neg i hT hαroot.1 hx hx1
  have hnA : n.val ∈ (SubgroupFunctor.range a).carrier (Over.mk (𝟙 _)) :=
    mul_mem (mul_mem (hneg _ hp.1) (hroot _ hx)) (hneg _ hp.2.1)
  -- points of `K` commute with points of `A` in `G`
  have hpointKA : ∀ (T : Over (Spec (CommRingCat.of k))) (z : T ⟶ K.X) (y : T ⟶ A.X),
      Commute (z ≫ (κ ≫ lG).hom.hom) (y ≫ a.hom.hom) := by
    intro T z y
    have h := (hc T y z).map (MonoidHom.mk' (fun w : T ⟶ Gα.X => w ≫ lG.hom.hom)
      (fun w w' => MonObj.mul_comp w w' lG.hom.hom))
    rw [← hlG]
    simpa only [MonoidHom.mk'_apply, Grp.comp_hom_hom, Category.assoc] using h.symm
  -- the generic cocharacter `2ν` has the same centralizer as `ν`
  have h2ν : IsGenericCocharacter i (2 • ν) := by
    intro r hr
    rw [map_nsmul]
    exact smul_ne_zero two_ne_zero (hν r hr)
  have hZ2 : Dynamic.centralizer (CommGroupScheme.groupHom (2 • ν) ≫ i) =
      Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i) := by
    rw [IsSplitTorus.dynamicCentralizer_eq_torusCentralizer hT i _ h2ν,
      IsSplitTorus.dynamicCentralizer_eq_torusCentralizer hT i ν hν]
  -- the reflection `n` acts on `S` through `σ`, and `ν + σ ∘ ν` is orthogonal to `α`
  let σ := normalizingAut i n
  have hσ : i ≫ (G.innerIso n.val).hom = CommGroupScheme.groupHom σ.hom ≫ i :=
    isNormalizingPoint_normalizingAut i n
  have hσα : σ.hom ≫ α = -α := by
    have h1 : σ.inv ≫ α = -α := by
      rw [← weylAction_apply]
      exact hnα
    calc σ.hom ≫ α = σ.hom ≫ (-(σ.inv ≫ α)) := by rw [h1, neg_neg]
      _ = -(σ.hom ≫ σ.inv ≫ α) := Preadditive.comp_neg _ _
      _ = -α := by rw [Iso.hom_inv_id_assoc]
  let ν' : cocharacterLattice S := ν ≫ σ.hom
  have hν'α : latticePairing S α (ν' + ν) = 0 := by
    rw [map_add, latticePairing_apply, latticePairing_apply]
    simp only [ν', Category.assoc, hσα, Preadditive.comp_neg, map_neg, neg_add_cancel]
  -- every point of `K` centralizes `ν`, hence lies in `M`
  have hKM : ∀ (T : Over (Spec (CommRingCat.of k))) (z : T ⟶ K.X),
      z ≫ (κ ≫ lG).hom.hom ∈
        (Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i)).carrier T := by
    intro T z
    rw [← hZ2, ← torusCentralizer_gm_eq_dynamicCentralizer]
    intro V c t
    let s := t ≫ (CommGroupScheme.groupHom ν ≫ i).hom.hom
    let N := G.constantPoint n.val V
    have hs2 : t ≫ (CommGroupScheme.groupHom (2 • ν) ≫ i).hom.hom = s * s := by
      rw [two_nsmul]
      simp only [s, Grp.comp_hom_hom, ← Category.assoc]
      rw [comp_groupHom_add, MonObj.mul_comp]
    have hdecomp : s * s = (s * N * s⁻¹ * N⁻¹) * (N * s * N⁻¹ * s) := by group
    have hψ : N * s * N⁻¹ * s = t ≫ (CommGroupScheme.groupHom (ν' + ν) ≫ i).hom.hom := by
      have h1 : N * s * N⁻¹ = t ≫ (CommGroupScheme.groupHom ν' ≫ i).hom.hom := by
        rw [← comp_innerIso_hom]
        have := congrArg (fun f => t ≫ (CommGroupScheme.groupHom ν).hom.hom ≫ f.hom.hom) hσ
        simp only [Grp.comp_hom_hom] at this
        simp only [s, ν', Grp.comp_hom_hom, Category.assoc, this]
        simp only [← Category.assoc]
        rw [← comp_groupHom_comp]
      rw [h1]
      simp only [s, Grp.comp_hom_hom, ← Category.assoc]
      rw [comp_groupHom_add, MonObj.mul_comp]
    rw [hs2, hdecomp]
    apply Commute.mul_right
    · have hNa : N ∈ (SubgroupFunctor.range a).carrier V := by
        change Over.homMk V.hom (by simp) ≫ n.val ∈ _
        exact (SubgroupFunctor.range a).comp_mem _ hnA
      have hsS : ∀ ζ' : cocharacterLattice S, latticePairing S α ζ' = 0 →
          s ∈ (Dynamic.centralizer (CommGroupScheme.groupHom ζ' ≫ i)).carrier V := by
        intro ζ' _
        apply torusCentralizer_le_dynamicCentralizer i (CommGroupScheme.groupHom ζ')
        apply range_le_torusCentralizer i
        exact SubgroupFunctor.mem_range.2 ⟨t ≫ (CommGroupScheme.groupHom ν).hom.hom, by
          simp only [s, Grp.comp_hom_hom, Category.assoc]⟩
      have hφ : s * N * s⁻¹ * N⁻¹ ∈ (SubgroupFunctor.range a).carrier V :=
        mul_mem (hnorm V s N hsS hNa) (inv_mem hNa)
      obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.1 hφ
      rw [← hy]
      simpa only [Category.assoc] using hpointKA V (c ≫ z) y
    · rw [hψ]
      have hL : c ≫ z ≫ (κ ≫ lG).hom.hom ∈ (Dynamic.centralizer χ).carrier V := by
        simpa only [Grp.comp_hom_hom, Category.assoc] using hpointL V (c ≫ z ≫ κ.hom.hom)
      have hmem := hLsub V _ hL (ν' + ν) hν'α
      rw [← torusCentralizer_gm_eq_dynamicCentralizer] at hmem
      simpa only [Category.id_comp] using hmem V (𝟙 V) t
  -- `K` factors through `M`, and, being perfect, through `D`
  have hKM' : SubgroupFunctor.range (κ ≫ lG) ≤
      Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i) := by
    intro T g hg
    obtain ⟨z, rfl⟩ := SubgroupFunctor.mem_range.1 hg
    exact hKM T z
  let κM : K ⟶ M := hj.factorHom (κ ≫ lG) hKM'
  have hκM : κM ≫ j = κ ≫ lG := hj.factorHom_comp (κ ≫ lG) hKM'
  have hKtop : derivedSubgroup K = ⊤ := semisimplePerfect k K hKss
  have hdrep : (SubgroupFunctor.range d).IsRepresentedBy d := ⟨hd.1.mono_hom, rfl⟩
  have hκD' : SubgroupFunctor.range κM ≤ SubgroupFunctor.range d := by
    intro T g hg
    obtain ⟨z, rfl⟩ := SubgroupFunctor.mem_range.1 hg
    rw [hd.2]
    apply mem_derivedSubgroup_comp κM
    rw [hKtop]
    trivial
  let κD : K ⟶ D := hdrep.factorHom κM hκD'
  have hκD : κD ≫ d = κM := hdrep.factorHom_comp κM hκD'
  -- `M` is closed and lies in `L`, so `D` lies in `Gα`
  have hjc : IsClosedSubgroup j := by
    have hrep' := Dynamic.Affine.isRepresentedBy_centralizerHom (CommGroupScheme.groupHom ν ≫ i)
    rw [← hj.isoOfIsRepresentedBy_hom_comp hrep']
    exact IsClosedSubgroup.iso_comp _ (Dynamic.Affine.isClosedSubgroup_centralizerHom _)
  have hMred : IsConnectedReductive M := dynamicCentralizerReductive k G hGred _ M j hjc hj
  have hML : SubgroupFunctor.range j ≤ Dynamic.centralizer χ := by
    rw [hj.2, IsSplitTorus.dynamicCentralizer_eq_torusCentralizer hT i ν hν]
    exact torusCentralizer_le_dynamicCentralizer i (CommGroupScheme.groupHom ζ)
  let jL : M ⟶ L := hl.factorHom j hML
  have hjL : jL ≫ l = j := hl.factorHom_comp j hML
  have hDGα : SubgroupFunctor.range (d ≫ jL) ≤ SubgroupFunctor.range dα := by
    intro T g hg
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.1 hg
    rw [hdα.2]
    have hy : y ≫ d.hom.hom ∈ (derivedSubgroup M).carrier T := by
      rw [← hd.2]
      exact SubgroupFunctor.mem_range.2 ⟨y, rfl⟩
    simpa only [Grp.comp_hom_hom, Category.assoc] using mem_derivedSubgroup_comp jL hy
  let δ : D ⟶ Gα := hdαrep.factorHom (d ≫ jL) hDGα
  have hδ : δ ≫ lG = d ≫ j := by
    have h1 : δ ≫ dα = d ≫ jL := hdαrep.factorHom_comp (d ≫ jL) hDGα
    simp only [lG]
    rw [← Category.assoc, h1, Category.assoc, hjL]
  have hκδ : κD ≫ δ = κ :=
    hlGrep.hom_ext (by rw [Category.assoc, hδ, ← Category.assoc, hκD, hκM])
  have hδmono : Mono δ.hom.hom := by
    have : Mono d.hom.hom := hd.1.mono_hom
    have : Mono j.hom.hom := hj.1
    have hm : Mono (δ.hom.hom ≫ lG.hom.hom) := by
      rw [← Grp.comp_hom_hom, hδ, Grp.comp_hom_hom]
      infer_instance
    exact mono_of_mono _ lG.hom.hom
  -- instances for the dichotomy in `D`
  have hDss : IsSemisimple D := derivedSubgroupSemisimple k M D d hMred hd
  have : Smooth D.X.hom := hDss.isConnectedReductive.smooth
  have : IsAffineHom D.X.hom := hDss.isConnectedReductive.isAffineHom
  have : Smooth K.X.hom := hKss.isConnectedReductive.smooth
  have : ConnectedSpace K.X.left := hKss.isConnectedReductive.connectedSpace
  have : IsAffineHom K.X.hom := hKss.isConnectedReductive.isAffineHom
  have hκDc : IsClosedSubgroup κD :=
    IsClosedSubgroup.of_comp (hd.1.comp hjc) (by
      rw [← Category.assoc, hκD, hκM]
      exact hκc.comp hlGc)
  have hκDn : (SubgroupFunctor.range κD).IsNormal := by
    intro T g x _ hx
    obtain ⟨z, rfl⟩ := SubgroupFunctor.mem_range.1 hx
    have hmem := hκn T (g ≫ δ.hom.hom) (z ≫ κ.hom.hom) trivial
      (SubgroupFunctor.mem_range.2 ⟨z, rfl⟩)
    obtain ⟨z', hz'⟩ := SubgroupFunctor.mem_range.1 hmem
    refine SubgroupFunctor.mem_range.2 ⟨z', ?_⟩
    apply (cancel_mono δ.hom.hom).1
    rw [hconj, Category.assoc, ← Grp.comp_hom_hom, hκδ, hz', ← hκδ]
    simp only [Grp.comp_hom_hom, Category.assoc]
  rcases hB.range_le_or_commute_of_normal b κD hbc hκDc hbn hκDn with hle | hcomm
  · -- `B` lies in `K`, which commutes with `A`
    right
    intro T x y
    obtain ⟨z, hz⟩ := SubgroupFunctor.mem_range.1 (hle T (SubgroupFunctor.mem_range.2 ⟨x, rfl⟩))
    have hxz : x ≫ (b ≫ d ≫ j).hom.hom = z ≫ (κ ≫ lG).hom.hom := by
      rw [← hκM, ← hκD]
      simp only [Grp.comp_hom_hom, ← Category.assoc, hz]
    rw [hxz]
    exact hpointKA T z y
  · -- `B` commutes with `K`: its projection to `K` is central, hence trivial
    left
    let mulAK := commutingSubgroupMultiplicationHom aG κ hc
    let pA : Gα ⟶ A := commutingFactorRetraction aG κ hc
    let q : Gα ⟶ K := inv mulAK ≫ snd A K
    have hdec : ∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ Gα.X),
        (g ≫ pA.hom.hom ≫ aG.hom.hom) * (g ≫ q.hom.hom ≫ κ.hom.hom) = g := by
      intro T g
      have hinv : (g ≫ (inv mulAK).hom.hom) ≫ mulAK.hom.hom = g := by
        rw [Category.assoc, ← Grp.comp_hom_hom, IsIso.inv_hom_id, Grp.id_hom_hom,
          Category.comp_id]
      have hmul := hinv
      simp only [mulAK, commutingSubgroupMultiplicationHom_hom, subgroupMultiplication,
        MonObj.comp_mul] at hmul
      simpa only [pA, q, commutingFactorRetraction, Grp.comp_hom_hom, Grp.fst_hom_hom,
        Grp.snd_hom_hom, Category.assoc] using hmul
    let f : B ⟶ K := b ≫ δ ≫ q
    have hcentral : ∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ B.X) (z : T ⟶ K.X),
        Commute (x ≫ f.hom.hom) z := by
      intro T x z
      let g := x ≫ (b ≫ δ).hom.hom
      have hgz : Commute g (z ≫ κ.hom.hom) := by
        have h := (hcomm T x z).map (MonoidHom.mk' (fun w : T ⟶ D.X => w ≫ δ.hom.hom)
          (fun w w' => MonObj.mul_comp w w' δ.hom.hom))
        rw [← hκδ]
        simpa only [MonoidHom.mk'_apply, g, Grp.comp_hom_hom, Category.assoc] using h
      have hfz : Commute (g ≫ pA.hom.hom ≫ aG.hom.hom) (z ≫ κ.hom.hom) :=
        by simpa only [Category.assoc] using hc T (g ≫ pA.hom.hom) z
      have hq : g ≫ q.hom.hom ≫ κ.hom.hom = (g ≫ pA.hom.hom ≫ aG.hom.hom)⁻¹ * g := by
        rw [eq_inv_mul_iff_mul_eq, hdec T g]
      have hqz : Commute (g ≫ q.hom.hom ≫ κ.hom.hom) (z ≫ κ.hom.hom) := by
        rw [hq]
        exact hfz.inv_left.mul_left hgz
      have : Mono κ.hom.hom := hκc.mono_hom
      apply (cancel_mono κ.hom.hom).1
      rw [MonObj.mul_comp, MonObj.mul_comp]
      have hfx : (x ≫ f.hom.hom) ≫ κ.hom.hom = g ≫ q.hom.hom ≫ κ.hom.hom := by
        simp only [f, g, Grp.comp_hom_hom, Category.assoc]
      rw [hfx]
      exact hqz.eq
    have hfcomm : (SubgroupFunctor.range (kernelι f)).ContainsCommutators := by
      intro T x y
      apply (mem_range_kernelι_iff f _).mpr
      have hxy := hcentral T x (y ≫ f.hom.hom)
      simp only [MonObj.mul_comp, GrpObj.inv_comp]
      rw [hxy.eq]
      group
    have hfone : ∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ B.X), x ≫ f.hom.hom = 1 := by
      intro T x
      have hx : x ∈ (derivedSubgroup B).carrier T := by
        rw [hB.derivedSubgroup_eq_top]
        trivial
      have hker := derivedSubgroup_le_range (kernelι f) (by
        change IsClosedImmersion (kernelι f).hom.hom.left
        infer_instance) hfcomm T hx
      exact (mem_range_kernelι_iff f _).mp hker
    intro T g hg
    obtain ⟨x, rfl⟩ := SubgroupFunctor.mem_range.1 hg
    let g' := x ≫ (b ≫ δ).hom.hom
    have hq1 : g' ≫ q.hom.hom = 1 := by
      simpa only [f, g', Grp.comp_hom_hom, Category.assoc] using hfone T x
    have hg' : g' = g' ≫ pA.hom.hom ≫ aG.hom.hom := by
      have h := hdec T g'
      rw [← Category.assoc g' q.hom.hom, hq1, MonObj.one_comp, mul_one] at h
      exact h.symm
    refine SubgroupFunctor.mem_range.2 ⟨g' ≫ pA.hom.hom, ?_⟩
    have hxg : x ≫ (b ≫ d ≫ j).hom.hom = g' ≫ lG.hom.hom := by
      have hbdj : b ≫ d ≫ j = b ≫ δ ≫ lG := by rw [hδ]
      rw [hbdj]
      simp only [g', Grp.comp_hom_hom, Category.assoc]
    calc (g' ≫ pA.hom.hom) ≫ a.hom.hom
        = (g' ≫ pA.hom.hom ≫ aG.hom.hom) ≫ lG.hom.hom := by
          rw [← hlG]
          simp only [Grp.comp_hom_hom, Category.assoc]
      _ = g' ≫ lG.hom.hom := by rw [← hg']
      _ = x ≫ (b ≫ d ≫ j).hom.hom := hxg.symm

end Langlands.GroupScheme
