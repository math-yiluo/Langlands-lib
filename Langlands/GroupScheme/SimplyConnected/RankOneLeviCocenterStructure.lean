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
# The derived group of the standard Levi subgroup of a simple relative root

For a rank-one Levi factor `A` of a simple relative root `α` of a simply connected group, the
derived group `E` of the standard Levi subgroup `L` of `{α}` retracts onto `A`, the kernel of the
retraction lies in the derived group `D` of the minimal Levi subgroup `M`, and `D` maps to `E`.
The construction repeats steps 1–7 of the proof of `rankOneLeviFactorDichotomy`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- The standard Levi subgroup `L` of a simple relative root `α`, its derived group `E`, the
inclusion `aE` of a rank-one Levi factor `A` for `α` into `E` with a retraction `pA` whose
kernel maps into the derived group `D` of the minimal Levi subgroup `M`, and the inclusion
`δ : D ⟶ E`. -/
theorem rankOneLeviFactor_derivedRetraction (k : Type u) [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom] (hsc : IsSimplyConnected G)
    (S : CommGroupScheme (Spec (CommRingCat.of k))) (i : S.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice S) (hν : IsGenericCocharacter i ν)
    (M : GroupScheme (Spec (CommRingCat.of k))) (j : M ⟶ G)
    (hj : (Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i)).IsRepresentedBy j)
    (α : characterLattice S) (hα : α ∈ simpleRelativeRoots i ν)
    (A : GroupScheme (Spec (CommRingCat.of k))) (a : A ⟶ G) (ha : IsRankOneLeviFactor i α a)
    (D : GroupScheme (Spec (CommRingCat.of k))) (d : D ⟶ M) (hd : IsDerivedSubgroup d) :
    ∃ (ζ : cocharacterLattice S) (L : GroupScheme (Spec (CommRingCat.of k))) (l : L ⟶ G)
      (jL : M ⟶ L) (E : GroupScheme (Spec (CommRingCat.of k))) (e : E ⟶ L) (aE : A ⟶ E)
      (pA : E ⟶ A) (δ : D ⟶ E),
      IsStandardCocharacter i ν {α} ζ ∧
      (Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ i)).IsRepresentedBy l ∧
      IsClosedSubgroup l ∧ IsConnectedReductive L ∧ jL ≫ l = j ∧ IsDerivedSubgroup e ∧
      aE ≫ e ≫ l = a ∧ aE ≫ pA = 𝟙 A ∧
      (∀ (T : Over (Spec (CommRingCat.of k))) (y : T ⟶ E.X), y ≫ pA.hom.hom = 1 →
        y ≫ (e ≫ l).hom.hom ∈ (SubgroupFunctor.range (d ≫ j)).carrier T) ∧
      δ ≫ e ≫ l = d ≫ j := by
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
  -- the retraction onto `A` and its kernel
  let pA : Gα ⟶ A := commutingFactorRetraction aG κ hc
  refine ⟨ζ, L, l, jL, Gα, dα, aG, pA, δ, hζ, hl, hlc, hLred, hjL, hdα, hlG,
    comp_commutingFactorRetraction aG κ hc, ?_, hδ⟩
  intro T y hy
  obtain ⟨n, rfl⟩ := SubgroupFunctor.mem_range.1
    ((comp_commutingFactorRetraction_eq_one_iff aG κ hc y).1 hy)
  refine SubgroupFunctor.mem_range.2 ⟨n ≫ κD.hom.hom, ?_⟩
  have h1 : κD ≫ d ≫ j = κ ≫ dα ≫ l := by
    rw [← Category.assoc, hκD, hκM]
  have h2 := congrArg (fun f => n ≫ f.hom.hom) h1
  simpa only [Grp.comp_hom_hom, Category.assoc] using h2

end Langlands.GroupScheme
