import Langlands.GroupScheme.Rational.RelativeWeylAbsoluteRestrictionStatement
import Langlands.GroupScheme.Rational.RelativeWeylGroupRestrictProof
import Langlands.GroupScheme.Rational.TorusNormalizerProof
import Langlands.GroupScheme.Rational.SplitTorusCentralizerReductiveProof
import Langlands.GroupScheme.Rational.MaximalSplitTorusConjugacyProof
import Langlands.GroupScheme.Rational.MaximalSplitTorusCentralizer
import Langlands.GroupScheme.Rational.MaximalSplitTorusSubgroup
import Langlands.GroupScheme.Rational.SplitRankTransport
import Langlands.GroupScheme.Rational.NormalizerGaloisAction
import Langlands.GroupScheme.Reductive.FieldExtensionProof
import Langlands.GroupScheme.Torus.MaximalBaseChangeForwardReduction
import Langlands.GroupScheme.Absolute.CocharacterDescentGroup

/-! # The relative Weyl group as restrictions of absolute Weyl elements: proof

Proof of `RelativeWeylAbsoluteRestrictionStatement` (Borel–Tits 1965, Corollaire 5.5).
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace SubgroupFunctor

variable {S S' : Scheme.{u}} (b : S' ⟶ S) {G : GroupScheme S}

/-- A point of `G_{S'}` normalizing the base change of a subgroup functor `F` corresponds,
under the pullback adjunction, to a point of `G` normalizing `F`. -/
theorem baseChangePointsEquiv_mem_normalizer (F : SubgroupFunctor G) {T : Over S'}
    {x : T ⟶ ((GroupScheme.baseChange b).obj G).X}
    (hx : x ∈ (F.baseChange b).normalizer.carrier T) :
    baseChangePointsEquiv b G T x ∈ F.normalizer.carrier ((Over.map b).obj T) := by
  intro V a y hy
  let V' : Over S' := Over.mk (a.left ≫ T.hom)
  let a' : V' ⟶ T := Over.homMk a.left rfl
  let e : V ≅ (Over.map b).obj V' := Over.isoMk (Iso.refl V.left) (by
    simpa [V'] using Over.w a)
  have hea : e.hom ≫ (Over.map b).map a' = a := by
    apply Over.OverMorphism.ext
    simp [e, a']
  let y' := (baseChangePointsEquiv b G V').symm (e.inv ≫ y)
  have hy' : y' ∈ (F.baseChange b).carrier V' := by
    rw [mem_baseChange, MulEquiv.apply_symm_apply]
    exact F.comp_mem e.inv hy
  obtain ⟨h₁, h₂⟩ := hx V' a' y' hy'
  rw [mem_baseChange, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply,
    baseChangePointsEquiv_naturality] at h₁ h₂
  have k₁ := F.comp_mem e.hom h₁
  have k₂ := F.comp_mem e.hom h₂
  simp only [MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, hea, Iso.hom_inv_id,
    Category.id_comp] at k₁ k₂
  exact ⟨k₁, k₂⟩

end SubgroupFunctor

section Field

variable {K : Type u} [Field K]

/-- **Borel–Tits 4.22 for a split subtorus of a maximal split torus.** Over a field, let
`a : A ⟶ G` be a split subtorus of a connected reductive group, contained through `f` in a
maximal split torus `j : T ⟶ G`. Every rational point normalizing `a` is a product `m * z` of
a rational point `m` normalizing both `a` and `j` and a rational point `z` centralizing `a`. -/
theorem exists_mul_of_mem_normalizerPoints_of_le_maximalSplitTorus
    {G : GroupScheme (Spec (CommRingCat.of K))} (hG : IsConnectedReductive G)
    {A T : CommGroupScheme (Spec (CommRingCat.of K))} {a : A.toGrp ⟶ G}
    (ha : IsSplitSubtorus a) {j : T.toGrp ⟶ G} (hj : IsMaximalSplitTorus j)
    (f : A.toGrp ⟶ T.toGrp) (hf : f ≫ j = a)
    {n : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X} (hn : n ∈ normalizerPoints a) :
    ∃ m ∈ normalizerPoints a ⊓ normalizerPoints j, ∃ z ∈ centralizerPoints a, n = m * z := by
  obtain ⟨σ, hσ⟩ := hn
  have hσ' : a ≫ (G.innerIso n).hom = CommGroupScheme.groupHom σ.hom ≫ a := hσ
  obtain ⟨-, M, ζ, hζc, -, hζ⟩ := torusNormalizerRepresentable K G hG A a ha
  have hM : IsConnectedReductive M := splitTorusCentralizerReductive K G hG A a ha.1 M ζ hζ
  have hj₁ : IsMaximalSplitTorus (j ≫ (G.innerIso n).hom) := hj.comp_iso _
  have hf₁ : (CommGroupScheme.groupHom σ.inv ≫ f) ≫ j ≫ (G.innerIso n).hom = a := by
    rw [Category.assoc, ← Category.assoc f j, hf, hσ', ← Category.assoc]
    change CommGroupScheme.groupHom (σ.inv ≫ σ.hom) ≫ a = a
    rw [Iso.inv_hom_id]
    exact Category.id_comp a
  have hcont : SubgroupFunctor.range j ≤ torusCentralizer a :=
    range_le_torusCentralizer_of_factor a j f hf
  have hcont₁ : SubgroupFunctor.range (j ≫ (G.innerIso n).hom) ≤ torusCentralizer a :=
    range_le_torusCentralizer_of_factor a _ _ hf₁
  obtain ⟨jM, hjM, hjMζ⟩ := hj.exists_lift hζ hζc hcont
  obtain ⟨j₁M, hj₁M, hj₁Mζ⟩ := hj₁.exists_lift hζ hζc hcont₁
  obtain ⟨g, e, hge⟩ := (maximalSplitTorusConjugacy K M hM).1 T T j₁M jM hj₁M hjM
  have hgc : IsNormalizingPoint a (g ≫ ζ.hom.hom) (Iso.refl A) := by
    change g ≫ ζ.hom.hom ∈ centralizerPoints a
    rw [← torusCentralizer_carrier_base, ← hζ.2]
    exact SubgroupFunctor.mem_range.2 ⟨g, rfl⟩
  have hconj : (j ≫ (G.innerIso n).hom) ≫ (G.innerIso (g ≫ ζ.hom.hom)).hom = e.hom ≫ j := by
    rw [← hj₁Mζ, Category.assoc, ← innerIso_hom_comp ζ g, ← Category.assoc, hge,
      Category.assoc, hjMζ]
  let e' : T ≅ T :=
    { hom := Additive.ofMul e.hom
      inv := Additive.ofMul e.inv
      hom_inv_id := congrArg Additive.ofMul e.hom_inv_id
      inv_hom_id := congrArg Additive.ofMul e.inv_hom_id }
  have hmj : IsNormalizingPoint j ((g ≫ ζ.hom.hom) * n) e' := by
    change j ≫ (G.innerIso ((g ≫ ζ.hom.hom) * n)).hom = e.hom ≫ j
    rw [innerIso_mul_hom, ← Category.assoc, hconj]
  have hma : IsNormalizingPoint a ((g ≫ ζ.hom.hom) * n) σ := by
    have h := IsNormalizingPoint.mul hgc hσ
    rwa [Iso.trans_refl] at h
  refine ⟨(g ≫ ζ.hom.hom) * n, ⟨⟨σ, hma⟩, ⟨e', hmj⟩⟩, ((g ≫ ζ.hom.hom) * n)⁻¹ * n, ?_,
    (mul_inv_cancel_left _ _).symm⟩
  have h := IsNormalizingPoint.mul hma.inv hσ
  rwa [Iso.self_symm_id] at h

end Field

section Extension

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

local notation "b" => algebraBaseMap k K
local notation "S_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b)
local notation "i_K" => CategoryTheory.Functor.map (GroupScheme.baseChange b)

/-- Conjunct 3: a `k`-point normalizing `i` through an automorphism whose base change is the
identity centralizes `i`. -/
theorem mem_centralizerPoints_of_baseChange_mapIso_eq_refl
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))} (i : S.toGrp ⟶ G)
    {n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X} {σ : S ≅ S}
    (hn : IsNormalizingPoint i n σ)
    (hσ : (CommGroupScheme.baseChange b).mapIso σ = Iso.refl _) :
    n ∈ centralizerPoints i := by
  have h := hn.baseChangeBasePoint b
  rw [hσ] at h
  have h' : (GroupScheme.baseChange b).map (i ≫ (G.innerIso n).hom) =
      (GroupScheme.baseChange b).map i := by
    rw [Functor.map_comp, baseChange_innerIso_hom]
    exact (isNormalizingPoint_refl_iff (T := S_K S)).1 h
  have : (Over.pullback b).Faithful := GaloisCocharacterDescent.faithful_algebraPullback k K
  rw [mem_centralizerPoints]
  apply Grp.hom_ext
  exact (Over.pullback b).map_injective (congrArg (fun f => f.hom.hom) h')

/-- Inclusion `⊇` of conjunct 2: the automorphism of `S_K` induced by a `K`-point normalizing
`S_K` is the base change of the automorphism induced by a `k`-point normalizing `S`. -/
theorem exists_isNormalizingPoint_baseChange_mapIso
    {G : GroupScheme (Spec (CommRingCat.of k))} (hG : IsConnectedReductive G)
    {S : CommGroupScheme (Spec (CommRingCat.of k))} {i : S.toGrp ⟶ G}
    (hi : IsMaximalSplitTorus i)
    {m : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ ((GroupScheme.baseChange b).obj G).X}
    {τ : S_K S ≅ S_K S} (hm : IsNormalizingPoint (i_K i) m τ) :
    ∃ (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) (σ : S ≅ S),
      IsNormalizingPoint i n σ ∧ (CommGroupScheme.baseChange b).mapIso σ = τ := by
  let U : Over (Spec (CommRingCat.of k)) := Over.mk b
  let eU : U ≅ (Over.map b).obj (Over.mk (𝟙 (Spec (CommRingCat.of K)))) :=
    Over.isoMk (Iso.refl _) (by simp [U])
  have hbase : ∀ x : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
      ((GroupScheme.baseChange b).obj G).X,
      baseChangeBasePointsEquiv b G x = eU.hom ≫ baseChangePointsEquiv b G _ x :=
    fun _ => rfl
  -- The transported point normalizes `i` over `U`.
  have hmN : m ∈ ((SubgroupFunctor.range i).baseChange b).normalizer.carrier
      (Over.mk (𝟙 (Spec (CommRingCat.of K)))) := by
    rw [← SubgroupFunctor.range_baseChangeHom]
    exact normalizerPoints_le_torusNormalizer (T := S_K S) (i_K i) ⟨τ, hm⟩
  have hm' : baseChangeBasePointsEquiv b G m ∈ (torusNormalizer i).carrier U := by
    rw [hbase]
    exact (torusNormalizer i).comp_mem eU.hom
      (SubgroupFunctor.baseChangePointsEquiv_mem_normalizer b _ hmN)
  have : ConnectedSpace U.left := by
    change ConnectedSpace (Spec (CommRingCat.of K))
    infer_instance
  obtain ⟨w, hw⟩ := (relativeWeylGroupRestrict_bijective k G hG S i hi U).2
    (QuotientGroup.mk ⟨_, hm'⟩)
  obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective w
  rw [relativeWeylGroupRestrict_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf] at hw
  obtain ⟨σ, hσ⟩ := n.2
  refine ⟨n, σ, hσ, ?_⟩
  -- The quotient of the two points over `U` centralizes `i`; transport it back to `K`.
  have hz : (baseChangeBasePoint b G n)⁻¹ * m ∈ centralizerPoints (T := S_K S) (i_K i) := by
    refine (torusCentralizer_carrier_base (T := S_K S) (i_K i)).le ?_
    rw [torusCentralizer_baseChange b i, SubgroupFunctor.mem_baseChange]
    have hzU : baseChangeBasePointsEquiv b G ((baseChangeBasePoint b G n)⁻¹ * m) ∈
        (torusCentralizer i).carrier U := by
      rw [map_mul, map_inv, baseChangeBasePoint, MulEquiv.apply_symm_apply]
      exact hw
    rw [hbase] at hzU
    have h := (torusCentralizer i).comp_mem eU.inv hzU
    rwa [Iso.inv_hom_id_assoc] at h
  have hnK := hσ.baseChangeBasePoint b
  have hmK : IsNormalizingPoint (T := S_K S) (i_K i)
      (baseChangeBasePoint b G n * ((baseChangeBasePoint b G n)⁻¹ * m))
      (Iso.refl _ ≪≫ (CommGroupScheme.baseChange b).mapIso σ) :=
    IsNormalizingPoint.mul hnK hz
  rw [mul_inv_cancel_left, Iso.refl_trans] at hmK
  have : Mono i.hom.hom.left := by
    have : IsClosedImmersion i.hom.hom.left := hi.1.2
    infer_instance
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  have hmono : Mono (i_K i).hom.hom.left := by
    change Mono ((Over.pullback b).map i.hom.hom).left
    infer_instance
  exact @IsNormalizingPoint.unique _ (S_K S) _ (i_K i) hmono _ _ _ hmK hm

end Extension

/-- **Borel–Tits 1965, Corollaire 5.5.** -/
theorem relativeWeylAbsoluteRestriction : RelativeWeylAbsoluteRestrictionStatement.{u} := by
  intro k K _ _ _ G hG S i hi T j f hj hf
  have hGK : IsConnectedReductive ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) :=
    connectedReductiveFieldExtensionStatement k K G hG
  have hSK : IsSplitSubtorus (T := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj S)
      ((GroupScheme.baseChange (algebraBaseMap k K)).map i) :=
    ⟨hi.1.1.baseChange _, hi.1.2.baseChange _⟩
  have h1 := fun n (hn : n ∈ normalizerPoints
      (T := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj S)
      ((GroupScheme.baseChange (algebraBaseMap k K)).map i)) =>
    exists_mul_of_mem_normalizerPoints_of_le_maximalSplitTorus hGK hSK hj
      (CommGroupScheme.groupHom f) hf hn
  refine ⟨h1, ?_, fun n σ hn hσ => mem_centralizerPoints_of_baseChange_mapIso_eq_refl i hn hσ⟩
  ext τ
  constructor
  · rintro ⟨n, σ, hn, rfl⟩
    obtain ⟨m, ⟨-, hmj⟩, z, hz, hnmz⟩ := h1 _ ⟨_, hn.baseChangeBasePoint _⟩
    refine ⟨m, hmj, ?_⟩
    have hz' : IsNormalizingPoint (T := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj S)
        ((GroupScheme.baseChange (algebraBaseMap k K)).map i) z⁻¹ (Iso.refl _).symm :=
      IsNormalizingPoint.inv hz
    have h := IsNormalizingPoint.mul (hn.baseChangeBasePoint (algebraBaseMap k K)) hz'
    rwa [hnmz, mul_inv_cancel_right, Iso.refl_symm, Iso.refl_trans] at h
  · rintro ⟨m, -, hm⟩
    exact exists_isNormalizingPoint_baseChange_mapIso hG hi hm

end Langlands.GroupScheme
