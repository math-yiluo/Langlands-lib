import Langlands.GroupScheme.CentralSurjection.DerivedMap
import Langlands.GroupScheme.Rational.SplitTorusFppfImage
import Langlands.GroupScheme.Rational.CentralSurjectionMaximalSplitTorusImageProof
import Langlands.GroupScheme.SubgroupFunctor.FpqcDescent
import Langlands.GroupScheme.ConjugacyBaseChange
import Langlands.GroupScheme.Rational.SplitTorusFactorization
import Langlands.GroupScheme.Derived.SemisimpleProof

/-!
# Split tori and their normalizers under a surjection with central kernel

* `exists_maximalSplitTorus_image`: for a surjective homomorphism `f : G → G'` of connected
  reductive groups with central kernel and a maximal split torus `i : S → G`, the closed image of
  `S` is a maximal split torus `i' : S' → G'`, reached from `S` by an fppf homomorphism
  `fS : S → S'` with `i ≫ f = fS ≫ i'`.
* `IsFppfTorusImage.normalizerPointsMap`: for any homomorphism `q : G → H`, split tori
  `i : T → G`, closed `j : T' → H` and an fppf `p : T → T'` with `p ≫ j = i ≫ q`, the map
  `n ↦ q(n)` sends the rational normalizer points of `i` to those of `j`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]

/-! ### The image of a maximal split torus -/

/-- The closed image of a maximal split torus under a surjection with central kernel is a maximal
split torus, reached by an fppf homomorphism of tori. -/
theorem exists_maximalSplitTorus_image {G G' : GroupScheme (Spec (CommRingCat.of k))}
    (hG : IsConnectedReductive G) (hG' : IsConnectedReductive G') (f : G ⟶ G')
    [Surjective f.hom.hom.left] (hf : IsCentral (kernelι f))
    {S : CommGroupScheme (Spec (CommRingCat.of k))} {i : S.toGrp ⟶ G}
    (hi : IsMaximalSplitTorus i) :
    ∃ (S' : CommGroupScheme (Spec (CommRingCat.of k))) (i' : S'.toGrp ⟶ G') (fS : S ⟶ S'),
      IsMaximalSplitTorus i' ∧ i ≫ f = CommGroupScheme.groupHom fS ≫ i' ∧
        Flat (CommGroupScheme.groupHom fS).hom.hom.left ∧
        Surjective (CommGroupScheme.groupHom fS).hom.hom.left ∧
        LocallyOfFinitePresentation (CommGroupScheme.groupHom fS).hom.hom.left := by
  have : Smooth G.X.hom := hG.smooth
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : Smooth G'.X.hom := hG'.smooth
  have : IsAffineHom G'.X.hom := hG'.isAffineHom
  have : QuasiCompact f.hom.hom.left := by
    have : QuasiCompact (f.hom.hom.left ≫ G'.X.hom) := by
      rw [Over.w]
      infer_instance
    exact QuasiCompact.of_comp f.hom.hom.left G'.X.hom
  have hflat : Flat f.hom.hom.left := flat_of_surjective f
  have : LocallyOfFiniteType f.hom.hom.left := by
    have : LocallyOfFiniteType (f.hom.hom.left ≫ G'.X.hom) := by
      rw [Over.w]
      infer_instance
    exact locallyOfFiniteType_of_comp _ G'.X.hom
  have : IsLocallyNoetherian G'.X.left := LocallyOfFiniteType.isLocallyNoetherian G'.X.hom
  have hlfp : LocallyOfFinitePresentation f.hom.hom.left :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  let I := hi.1.1.fppfImage (i ≫ f)
  exact ⟨I.torus, I.inclusion, I.projection,
    centralSurjectionMaximalSplitTorusImage k G G' f hG hG' hflat inferInstance hlfp hf S I.torus
      i I.inclusion I.projection hi I.isSplitSubtorus I.flat I.surjective
      I.locallyOfFinitePresentation I.factorization,
    I.factorization.symm, I.flat, I.surjective, I.locallyOfFinitePresentation⟩

/-! ### Normalizer points under an fppf torus image -/

/-- `j : T' → H` is a closed subgroup and receives `i : T → G` along `q : G → H` through an fppf
homomorphism of tori `p : T → T'`. -/
structure IsFppfTorusImage {G H : GroupScheme (Spec (CommRingCat.of k))}
    {T T' : CommGroupScheme (Spec (CommRingCat.of k))}
    (q : G ⟶ H) (i : T.toGrp ⟶ G) (j : T'.toGrp ⟶ H) (p : T ⟶ T') : Prop where
  isClosedSubgroup : IsClosedSubgroup j
  comp_eq : CommGroupScheme.groupHom p ≫ j = i ≫ q
  flat : Flat (CommGroupScheme.groupHom p).hom.hom.left
  surjective : Surjective (CommGroupScheme.groupHom p).hom.hom.left
  locallyOfFinitePresentation :
    LocallyOfFinitePresentation (CommGroupScheme.groupHom p).hom.hom.left

namespace IsFppfTorusImage

variable {G H : GroupScheme (Spec (CommRingCat.of k))}
  {T T' : CommGroupScheme (Spec (CommRingCat.of k))}
  {q : G ⟶ H} {i : T.toGrp ⟶ G} {j : T'.toGrp ⟶ H} {p : T ⟶ T'}
  (h : IsFppfTorusImage q i j p)

include h

/-- Conjugation by `q(n)`, for `n` normalizing `T`, maps the range of `j` into itself: after the
fppf base change along `p`, every point of `T'` comes from `T`. -/
theorem conjugate_range_le {n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X}
    {σ : T ≅ T} (hn : IsNormalizingPoint i n σ) :
    SubgroupFunctor.range (j ≫ (H.innerIso (n ≫ q.hom.hom)).hom) ≤
      SubgroupFunctor.range j := by
  let : IsClosedImmersion j.hom.hom.left := h.isClosedSubgroup
  let : Mono j.hom.hom := Over.mono_of_mono_left _
  let : Flat (CommGroupScheme.groupHom p).hom.hom.left := h.flat
  let : Surjective (CommGroupScheme.groupHom p).hom.hom.left := h.surjective
  let : LocallyOfFinitePresentation (CommGroupScheme.groupHom p).hom.hom.left :=
    h.locallyOfFinitePresentation
  have hsquare :
      CommGroupScheme.groupHom p ≫ j ≫ (H.innerIso (n ≫ q.hom.hom)).hom =
        CommGroupScheme.groupHom σ.hom ≫ CommGroupScheme.groupHom p ≫ j := by
    calc
      _ = i ≫ q ≫ (H.innerIso (n ≫ q.hom.hom)).hom := by
        rw [← Category.assoc, h.comp_eq, Category.assoc]
      _ = i ≫ (G.innerIso n).hom ≫ q := by rw [innerIso_hom_comp]
      _ = CommGroupScheme.groupHom σ.hom ≫ i ≫ q := by
        rw [← Category.assoc, hn, Category.assoc]
      _ = _ := by rw [← h.comp_eq]
  rintro U x ⟨y, rfl⟩
  let V : Over (Spec (CommRingCat.of k)) :=
    Over.mk (pullback.fst y.left (CommGroupScheme.groupHom p).hom.hom.left ≫ U.hom)
  let a : V ⟶ U :=
    Over.homMk (pullback.fst y.left (CommGroupScheme.groupHom p).hom.hom.left) rfl
  let z : V ⟶ T.toGrp.X :=
    Over.homMk (pullback.snd y.left (CommGroupScheme.groupHom p).hom.hom.left) (by
      rw [← Over.w (CommGroupScheme.groupHom p).hom.hom, ← Category.assoc,
        ← pullback.condition, Category.assoc, Over.w y]
      rfl)
  have haz : a ≫ y = z ≫ (CommGroupScheme.groupHom p).hom.hom :=
    Over.OverMorphism.ext pullback.condition
  have : Flat a.left := by change Flat (pullback.fst _ _); infer_instance
  have : Surjective a.left := by change Surjective (pullback.fst _ _); infer_instance
  have : LocallyOfFinitePresentation a.left := by
    change LocallyOfFinitePresentation (pullback.fst _ _)
    infer_instance
  apply SubgroupFunctor.mem_range_of_comp_mem_range j a
  refine SubgroupFunctor.mem_range.mpr
    ⟨z ≫ (CommGroupScheme.groupHom σ.hom).hom.hom ≫
      (CommGroupScheme.groupHom p).hom.hom, ?_⟩
  change (z ≫ (CommGroupScheme.groupHom σ.hom).hom.hom ≫
      (CommGroupScheme.groupHom p).hom.hom) ≫ j.hom.hom =
    a ≫ (y ≫ (j ≫ (H.innerIso (n ≫ q.hom.hom)).hom).hom.hom)
  have hs := congrArg (fun f => f.hom.hom) hsquare
  simp only [Grp.comp_hom_hom] at hs ⊢
  rw [← Category.assoc a y, haz]
  simpa only [Category.assoc] using congrArg (fun f => z ≫ f) hs.symm

/-- Conjugation by `q(n)` restricted to `T'`. -/
def normalizerEnd (n : normalizerPoints i) : T'.toGrp ⟶ T'.toGrp :=
  letI : IsClosedImmersion j.hom.hom.left := h.isClosedSubgroup
  letI : Mono j.hom.hom := Over.mono_of_mono_left _
  (show (SubgroupFunctor.range j).IsRepresentedBy j from ⟨inferInstance, rfl⟩).factorHom
    (j ≫ (H.innerIso (n.val ≫ q.hom.hom)).hom)
    (h.conjugate_range_le (isNormalizingPoint_normalizingAut i n))

theorem normalizerEnd_comp (n : normalizerPoints i) :
    h.normalizerEnd n ≫ j = j ≫ (H.innerIso (n.val ≫ q.hom.hom)).hom := by
  let : IsClosedImmersion j.hom.hom.left := h.isClosedSubgroup
  let : Mono j.hom.hom := Over.mono_of_mono_left _
  exact SubgroupFunctor.IsRepresentedBy.factorHom_comp _ _ _

theorem normalizerEnd_inv (n : normalizerPoints i) :
    h.normalizerEnd n ≫ h.normalizerEnd n⁻¹ = 𝟙 T'.toGrp := by
  let : IsClosedImmersion j.hom.hom.left := h.isClosedSubgroup
  let : Mono j.hom.hom := Over.mono_of_mono_left _
  apply (show (SubgroupFunctor.range j).IsRepresentedBy j from
    ⟨inferInstance, rfl⟩).hom_ext
  rw [Category.assoc, h.normalizerEnd_comp, ← Category.assoc,
    h.normalizerEnd_comp, Category.assoc, Category.id_comp]
  change j ≫ (H.innerIso (n.val ≫ q.hom.hom)).hom ≫
    (H.innerIso (n.val⁻¹ ≫ q.hom.hom)).hom = j
  rw [GrpObj.inv_comp, innerIso_inv_hom, Iso.hom_inv_id, Category.comp_id]

/-- Conjugation by `q(n)` restricts to an automorphism of `T'`. -/
def normalizerAut (n : normalizerPoints i) : T' ≅ T' where
  hom := Additive.ofMul (h.normalizerEnd n)
  inv := Additive.ofMul (h.normalizerEnd n⁻¹)
  hom_inv_id := congrArg Additive.ofMul (h.normalizerEnd_inv n)
  inv_hom_id := by
    have hi := h.normalizerEnd_inv n⁻¹
    rw [inv_inv] at hi
    exact congrArg Additive.ofMul hi

theorem isNormalizingPoint_normalizerAut (n : normalizerPoints i) :
    IsNormalizingPoint j (n.val ≫ q.hom.hom) (h.normalizerAut n) :=
  (h.normalizerEnd_comp n).symm

/-- `q` restricts to a homomorphism of rational normalizer points. -/
def normalizerPointsMap : normalizerPoints i →* normalizerPoints j where
  toFun n := ⟨n.val ≫ q.hom.hom, ⟨h.normalizerAut n, h.isNormalizingPoint_normalizerAut n⟩⟩
  map_one' := Subtype.ext (MonObj.one_comp _)
  map_mul' n m := Subtype.ext (MonObj.mul_comp n.val m.val _)

@[simp] theorem normalizerPointsMap_apply (n : normalizerPoints i) :
    (h.normalizerPointsMap n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X) =
      n.val ≫ q.hom.hom := rfl

/-- The rational points form: `q(n)` normalizes `T'` when `n` normalizes `T`. -/
theorem map_mem_normalizerPoints {n : rationalPoints G} (hn : n ∈ normalizerPoints i) :
    rationalPoints.map q n ∈ normalizerPoints j :=
  (h.normalizerPointsMap ⟨n, hn⟩).property

end IsFppfTorusImage

/-! ### The derived maximal split tori -/

section DerivedTorus

variable {G G' D D' : GroupScheme (Spec (CommRingCat.of k))}
  {S S' T T' : CommGroupScheme (Spec (CommRingCat.of k))}
  {d : D ⟶ G} {d' : D' ⟶ G'} {i : S.toGrp ⟶ G} {i' : S'.toGrp ⟶ G'}
  {j : T.toGrp ⟶ D} {j' : T'.toGrp ⟶ D'} {e : T ⟶ S} {e' : T' ⟶ S'} {fS : S ⟶ S'}

/-- Let `T ⊆ S ∩ D` and `T' ⊆ S' ∩ D'` be maximal split tori of the derived subgroups, with
`i ≫ f = fS ≫ i'`. Then `f_D : D → D'` maps `T` onto `T'` by an isogeny `t` compatible with
`fS`. The image of `T` commutes with `T'` (both lie in the commutative `S'`), so `T → D'` factors
through the maximal split torus `T'`; the closed image of `T` in `T'` is a maximal split torus of
`D'` (`centralSurjectionMaximalSplitTorusImage` for the central isogeny `f_D`), hence all of `T'`. -/
theorem exists_derivedTorus_isogeny (hG : IsConnectedReductive G)
    (hG' : IsConnectedReductive G') (hd : IsDerivedSubgroup d) (hd' : IsDerivedSubgroup d')
    (f : G ⟶ G') [Surjective f.hom.hom.left] (hf : IsCentral (kernelι f))
    (hi' : IsSplitSubtorus i') (hfS : i ≫ f = CommGroupScheme.groupHom fS ≫ i')
    (hj : IsMaximalSplitTorus j) (hj' : IsMaximalSplitTorus j')
    (he : j ≫ d = CommGroupScheme.groupHom e ≫ i)
    (he' : j' ≫ d' = CommGroupScheme.groupHom e' ≫ i') :
    ∃ t : T ⟶ T', j ≫ hd.map hd' f = CommGroupScheme.groupHom t ≫ j' ∧ t ≫ e' = e ≫ fS ∧
      IsIsogeny (CommGroupScheme.groupHom t) := by
  have hfD := hd.isCentralIsogeny_map hd' f hG hG' hf
  have : Mono d'.hom.hom := hd'.isRepresentedBy.1
  have : IsClosedImmersion i'.hom.hom.left := hi'.2
  have : Mono i'.hom.hom := Over.mono_of_mono_left _
  have hcomp : hd.map hd' f ≫ d' = d ≫ f := IsDerivedSubgroup.map_comp hd hd' f
  -- the image of `T` in `G'` lies in `S'`
  have hb : (j ≫ hd.map hd' f) ≫ d' =
      (CommGroupScheme.groupHom e ≫ CommGroupScheme.groupHom fS) ≫ i' := by
    rw [Category.assoc, hcomp, ← Category.assoc, he, Category.assoc, hfS, Category.assoc]
  have hbj : ∀ (U : Over (Spec (CommRingCat.of k))) (x : U ⟶ T.X) (y : U ⟶ T'.X),
      Commute (x ≫ (j ≫ hd.map hd' f).hom.hom) (y ≫ j'.hom.hom) := by
    intro U x y
    apply (commute_iff_eq _ _).mpr
    apply (cancel_mono d'.hom.hom).mp
    have hx : (x ≫ (j ≫ hd.map hd' f).hom.hom) ≫ d'.hom.hom =
        (x ≫ (CommGroupScheme.groupHom e ≫ CommGroupScheme.groupHom fS).hom.hom) ≫
          i'.hom.hom := by
      simpa only [Grp.comp_hom_hom, Category.assoc] using
        congrArg (fun z => x ≫ z.hom.hom) hb
    have hy : (y ≫ j'.hom.hom) ≫ d'.hom.hom =
        (y ≫ (CommGroupScheme.groupHom e').hom.hom) ≫ i'.hom.hom := by
      simpa only [Grp.comp_hom_hom, Category.assoc] using
        congrArg (fun z => y ≫ z.hom.hom) he'
    rw [MonObj.mul_comp, MonObj.mul_comp, hx, hy, ← MonObj.mul_comp, ← MonObj.mul_comp,
      mul_comm]
  have : IsAffineHom G'.X.hom := hG'.isAffineHom
  have : IsAffineHom D'.X.hom := by
    have : IsClosedImmersion d'.hom.hom.left := hd'.1
    rw [← Over.w d'.hom.hom]
    infer_instance
  obtain ⟨t₀, ht₀⟩ := hj'.exists_factor_of_commute hj.1.1 (j ≫ hd.map hd' f) hbj
  -- `t₀` is an isogeny
  have : IsAffineHom T'.X.hom := hj'.1.1.isAffineHom
  let I := hj.1.1.fppfImage t₀
  have : IsClosedImmersion I.inclusion.hom.hom.left := I.isSplitSubtorus.2
  have : IsClosedImmersion j'.hom.hom.left := hj'.1.2
  have hsub : IsSplitSubtorus (I.inclusion ≫ j') := by
    refine ⟨I.isSplitSubtorus.1, ?_⟩
    change IsClosedImmersion (I.inclusion.hom.hom.left ≫ j'.hom.hom.left)
    infer_instance
  have hD : IsConnectedReductive D := (derivedSubgroupSemisimple k G D d hG hd).isConnectedReductive
  have hD' : IsConnectedReductive D' :=
    (derivedSubgroupSemisimple k G' D' d' hG' hd').isConnectedReductive
  have hmax : IsMaximalSplitTorus (I.inclusion ≫ j') :=
    centralSurjectionMaximalSplitTorusImage k D D' (hd.map hd' f) hD hD' hfD.flat
      hfD.surjective hfD.locallyOfFinitePresentation hfD.isCentral_kernelι T I.torus j
      (I.inclusion ≫ j') I.projection hj hsub I.flat I.surjective I.locallyOfFinitePresentation
      (by rw [← Category.assoc, I.factorization, ht₀])
  have hiso : IsIso I.inclusion := hmax.2 T' j' hj'.1 I.inclusion rfl
  have hiso' : IsIso I.inclusion.hom.hom.left :=
    (inferInstance : IsIso ((Over.forget _).mapIso ((Grp.forget _).mapIso
      (asIso I.inclusion))).hom)
  have ht₀p : t₀.hom.hom.left =
      (CommGroupScheme.groupHom I.projection).hom.hom.left ≫ I.inclusion.hom.hom.left := by
    rw [← Over.comp_left, ← Grp.comp_hom_hom, I.factorization]
  have : Flat (CommGroupScheme.groupHom I.projection).hom.hom.left := I.flat
  have : Surjective (CommGroupScheme.groupHom I.projection).hom.hom.left := I.surjective
  have hfl : Flat t₀.hom.hom.left := by
    rw [ht₀p]
    infer_instance
  have hsu : Surjective t₀.hom.hom.left := by
    rw [ht₀p]
    infer_instance
  have : IsFinite (hd.map hd' f).hom.hom.left := hfD.isFinite
  have : IsClosedImmersion j.hom.hom.left := hj.1.2
  have hfi : IsFinite t₀.hom.hom.left := by
    have : IsFinite (t₀.hom.hom.left ≫ j'.hom.hom.left) := by
      rw [← Over.comp_left, ← Grp.comp_hom_hom, ht₀, Grp.comp_hom_hom, Over.comp_left]
      infer_instance
    exact IsFinite.of_comp t₀.hom.hom.left j'.hom.hom.left
  refine ⟨Additive.ofMul t₀, ht₀.symm, ?_, ⟨hfi, hfl, hsu⟩⟩
  have key : (t₀ ≫ CommGroupScheme.groupHom e') ≫ i' =
      (CommGroupScheme.groupHom e ≫ CommGroupScheme.groupHom fS) ≫ i' := by
    rw [Category.assoc, ← he', ← Category.assoc, ht₀, hb]
  apply CommGroupScheme.hom_ext_points
  intro U x
  apply (cancel_mono i'.hom.hom).mp
  have h := congrArg (fun z => x ≫ z.hom.hom) key
  simp only [Grp.comp_hom_hom, Category.assoc] at h
  rw [comp_groupHom_comp, comp_groupHom_comp]
  simp only [Category.assoc]
  exact h

end DerivedTorus

end Langlands.GroupScheme
