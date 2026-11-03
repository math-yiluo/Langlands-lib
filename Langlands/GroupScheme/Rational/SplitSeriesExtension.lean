import Langlands.GroupScheme.Rational.SplitUnipotentTransport
import Langlands.GroupScheme.GeometricConnectedness
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_GeometricallyConnected_descendsAlong_surjective
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Langlands.GroupScheme.Rational.MinimalPseudoParabolicRangeReduction

/-! # Extensions of split series along fppf quotients -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

section Torsor

variable {B : Scheme.{u}} {N P Q : GroupScheme B}

/-- The points of a subgroup with the same image as the kernel of `q` lie in that kernel. -/
theorem comp_eq_one_of_range_kernelι_eq {j : N ⟶ P} {q : P ⟶ Q}
    (hker : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range j) :
    j.hom.hom ≫ q.hom.hom = 1 := by
  have hmem : 𝟙 N.X ≫ j.hom.hom ∈ (SubgroupFunctor.range j).carrier N.X :=
    ⟨𝟙 N.X, rfl⟩
  rw [← hker, mem_range_kernelι_iff] at hmem
  simpa using hmem

/-- The right translation action of `N` on `P` through `j`: on points, `(p, n) ↦ p * j n`. -/
def translationAction (j : N ⟶ P) : P.X ⊗ N.X ⟶ P.X :=
  fst P.X N.X * (snd P.X N.X ≫ j.hom.hom)

theorem comp_translationAction (j : N ⟶ P) {T : Over B} (m : T ⟶ P.X ⊗ N.X) :
    m ≫ translationAction j = (m ≫ fst P.X N.X) * ((m ≫ snd P.X N.X) ≫ j.hom.hom) := by
  rw [translationAction, MonObj.comp_mul, Category.assoc]

/-- The torsor square of an exact kernel: `P × N ⇉ P → Q`, by the first projection and by
right translation, is a fibre product of `q` with itself. -/
theorem isPullback_translationAction {j : N ⟶ P} {q : P ⟶ Q} [Mono j.hom.hom]
    (hker : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range j) :
    IsPullback (fst P.X N.X) (translationAction j) q.hom.hom q.hom.hom := by
  have hjq := comp_eq_one_of_range_kernelι_eq hker
  have hlift : ∀ {T : Over B} (x : T ⟶ P.X), x ≫ q.hom.hom = 1 →
      ∃ y : T ⟶ N.X, y ≫ j.hom.hom = x := by
    intro T x hx
    have hmem : x ∈ (SubgroupFunctor.range (kernelι q)).carrier T :=
      (mem_range_kernelι_iff q x).mpr hx
    rw [hker] at hmem
    exact hmem
  have hw : fst P.X N.X ≫ q.hom.hom = translationAction j ≫ q.hom.hom := by
    rw [translationAction, MonObj.mul_comp, Category.assoc, hjq, MonObj.comp_one, mul_one]
  have hdiff : ∀ {T : Over B} (x x' : T ⟶ P.X), x ≫ q.hom.hom = x' ≫ q.hom.hom →
      ∃ y : T ⟶ N.X, y ≫ j.hom.hom = x⁻¹ * x' := by
    intro T x x' h
    apply hlift
    rw [MonObj.mul_comp, GrpObj.inv_comp, h, inv_mul_cancel]
  refine IsPullback.of_isLimit' ⟨hw⟩ ?_
  refine PullbackCone.IsLimit.mk hw
    (fun s => lift s.fst (Classical.choose (hdiff s.fst s.snd s.condition))) ?_ ?_ ?_
  · intro s
    exact lift_fst _ _
  · intro s
    rw [comp_translationAction, lift_fst, lift_snd,
      Classical.choose_spec (hdiff s.fst s.snd s.condition), mul_inv_cancel_left]
  · intro s m hfst hsnd
    apply CartesianMonoidalCategory.hom_ext
    · rw [lift_fst]
      exact hfst
    · rw [lift_snd]
      apply (cancel_mono j.hom.hom).mp
      rw [Classical.choose_spec (hdiff s.fst s.snd s.condition), ← hsnd, ← hfst,
        comp_translationAction, inv_mul_cancel_left]

end Torsor

section Descent

variable {B : Scheme.{u}} {N P Q : GroupScheme B}

/-- The torsor square of an exact kernel, on underlying schemes. -/
theorem isPullback_translationAction_left {j : N ⟶ P} {q : P ⟶ Q} [Mono j.hom.hom]
    (hker : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range j) :
    IsPullback (pullback.fst P.X.hom N.X.hom) (translationAction j).left
      q.hom.hom.left q.hom.hom.left :=
  (isPullback_translationAction hker).map (Over.forget B)

/-- Smoothness descends from the kernel to a quasi-compact fppf quotient map. -/
theorem smooth_of_range_kernelι_eq {j : N ⟶ P} {q : P ⟶ Q} [Mono j.hom.hom]
    (hker : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range j)
    [Flat q.hom.hom.left] [Surjective q.hom.hom.left] [QuasiCompact q.hom.hom.left]
    [Smooth N.X.hom] : Smooth q.hom.hom.left :=
  MorphismProperty.of_isPullback_of_descendsAlong
    (P := @Smooth) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    (isPullback_translationAction_left hker) ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
    (MorphismProperty.of_isPullback (IsPullback.of_hasPullback P.X.hom N.X.hom).flip
      inferInstance)

/-- Geometric connectedness descends from the kernel to a surjective quotient map. -/
theorem geometricallyConnected_of_range_kernelι_eq {j : N ⟶ P} {q : P ⟶ Q} [Mono j.hom.hom]
    (hker : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range j)
    [Surjective q.hom.hom.left] [GeometricallyConnected N.X.hom] :
    GeometricallyConnected q.hom.hom.left := by
  have := GeometricallyConnected.descendsAlong_surjective.{u}
  exact MorphismProperty.of_isPullback_of_descendsAlong
    (P := @GeometricallyConnected) (Q := @Surjective)
    (isPullback_translationAction_left hker) inferInstance
    (MorphismProperty.of_isPullback (IsPullback.of_hasPullback P.X.hom N.X.hom).flip
      inferInstance)

end Descent

section Extension

variable {B : Scheme.{u}}

private theorem isIso_hom_left {H H' : GroupScheme B} (e : H ≅ H') :
    IsIso e.hom.hom.hom.left :=
  (inferInstance : IsIso (((Grp.forget (Over B)) ⋙ Over.forget B).map e.hom))

/-- A monomorphic homomorphism with the same image as a closed subgroup is a closed
subgroup. -/
theorem IsClosedSubgroup.of_range_eq {K G N : GroupScheme B} {i : K ⟶ G} {j : N ⟶ G}
    (hj : IsClosedSubgroup j) [Mono i.hom.hom]
    (h : SubgroupFunctor.range i = SubgroupFunctor.range j) : IsClosedSubgroup i := by
  have : IsClosedImmersion j.hom.hom.left := hj
  have : Mono j.hom.hom := Over.mono_of_mono_left _
  let hi : (SubgroupFunctor.range i).IsRepresentedBy i := ⟨inferInstance, rfl⟩
  let hj' : (SubgroupFunctor.range i).IsRepresentedBy j := ⟨inferInstance, h.symm⟩
  have he := hi.isoOfIsRepresentedBy_hom_comp hj'
  have := isIso_hom_left (hi.isoOfIsRepresentedBy hj')
  change IsClosedImmersion i.hom.hom.left
  rw [← he]
  change IsClosedImmersion ((hi.isoOfIsRepresentedBy hj').hom.hom.hom.left ≫ j.hom.hom.left)
  infer_instance

/-- The kernel of a homomorphism is a normal subgroup functor. -/
theorem isNormal_range_kernelι {G H : GroupScheme B} (f : G ⟶ H) :
    (SubgroupFunctor.range (kernelι f)).IsNormal := by
  intro T g x _ hx
  rw [mem_range_kernelι_iff] at hx ⊢
  rw [MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp, hx, mul_one, mul_inv_cancel]

/-- **Extension closure of split series.** Let `j : N ⟶ P` be a closed subgroup with a split
series of length `m`, smooth and geometrically connected over the base, and let `q : P ⟶ Q` be a
quasi-compact fppf quotient map with kernel exactly `N`. If `Q` has a split series of length `n`,
then `P` has a split series of length `m + n`. -/
theorem HasSplitSeries.of_fppfQuotient {m : ℕ} {N : GroupScheme B} [Smooth N.X.hom]
    [GeometricallyConnected N.X.hom] (hN : HasSplitSeries m N) (n : ℕ) :
    ∀ {P Q : GroupScheme B} (j : N ⟶ P) (q : P ⟶ Q), IsClosedSubgroup j →
      QuasiCompact q.hom.hom.left → IsFppfQuotient (SubgroupFunctor.range j) q →
      HasSplitSeries n Q → HasSplitSeries (m + n) P := by
  induction n with
  | zero =>
    intro P Q j q hj _ hq hQ
    have hrange : SubgroupFunctor.range j = SubgroupFunctor.range (𝟙 P) := by
      rw [← hq.2.2.2]
      apply SubgroupFunctor.ext
      intro T
      ext x
      rw [mem_range_kernelι_iff]
      constructor
      · intro _
        exact SubgroupFunctor.mem_range.mpr ⟨x, by
          change x ≫ 𝟙 P.X = x
          exact Category.comp_id _⟩
      · intro _
        have hx : x ≫ q.hom.hom ∈ (SubgroupFunctor.range (𝟙 Q)).carrier T :=
          SubgroupFunctor.mem_range.mpr ⟨x ≫ q.hom.hom, by
            change (x ≫ q.hom.hom) ≫ 𝟙 Q.X = _
            exact Category.comp_id _⟩
        rw [hQ, SubgroupFunctor.bot_carrier, Subgroup.mem_bot] at hx
        exact hx
    have hid : IsClosedSubgroup (𝟙 P) := by
      show IsClosedImmersion (𝟙 P.X.left)
      infer_instance
    exact HasSplitSeries.of_iso (IsClosedSubgroup.sourceIsoOfRangeEq hj hid hrange) hN
  | succ n ih =>
    intro P Q j q hj hqc hq hQ
    obtain ⟨K', V, j', q', hj', hsmooth', hconn', -, hquot', hvector, hseries'⟩ := hQ
    obtain ⟨hflat, hsurj, hlfp, hker⟩ := hq
    obtain ⟨hflat', hsurj', hlfp', hker'⟩ := hquot'
    have : IsClosedImmersion j.hom.hom.left := hj
    have : Mono j.hom.hom := Over.mono_of_mono_left _
    have : Flat q.hom.hom.left := hflat
    have : Surjective q.hom.hom.left := hsurj
    have : LocallyOfFinitePresentation q.hom.hom.left := hlfp
    have : QuasiCompact q.hom.hom.left := hqc
    have : Flat q'.hom.hom.left := hflat'
    have : Surjective q'.hom.hom.left := hsurj'
    have : LocallyOfFinitePresentation q'.hom.hom.left := hlfp'
    have : Smooth q.hom.hom.left := smooth_of_range_kernelι_eq hker
    have : GeometricallyConnected q.hom.hom.left :=
      geometricallyConnected_of_range_kernelι_eq hker
    have hjq := comp_eq_one_of_range_kernelι_eq hker
    -- the kernel of `q'`, identified with `K'`
    have hι' : IsClosedSubgroup (kernelι q') := IsClosedSubgroup.of_range_eq hj' hker'
    have : IsClosedImmersion (kernelι q').hom.hom.left := hι'
    let e : K' ≅ kernel q' := IsClosedSubgroup.sourceIsoOfRangeEq hj' hι' hker'.symm
    have : IsIso e.inv.hom.hom.left := isIso_hom_left e.symm
    have : IsIso e.hom.hom.hom.left := isIso_hom_left e
    have : Smooth K'.X.hom := hsmooth'
    have : Smooth (kernel q').X.hom := by
      rw [← Over.w e.inv.hom.hom]
      infer_instance
    have : ConnectedSpace (kernel q').X.left :=
      (e.hom.hom.hom.left).homeomorph.connectedSpace_iff.mp hconn'
    -- the preimage of the kernel of `q'`
    let i₁ := kernelι (q ≫ q')
    let q₁ : kernel (q ≫ q') ⟶ kernel q' :=
      pullback.lift (i₁ ≫ q) (pullback.snd (q ≫ q') (kernelUnit V)) (by
        rw [Category.assoc]
        exact pullback.condition)
    have hq₁ : q₁ ≫ kernelι q' = i₁ ≫ q := pullback.lift_fst _ _ _
    have hsq : IsPullback q₁.hom.hom.left i₁.hom.hom.left (kernelι q').hom.hom.left
        q.hom.hom.left := by
      have hout := (kernel_isPullback (q ≫ q')).flip
      have hright := (kernel_isPullback q').flip
      rw [Grp.comp_hom_hom] at hout
      have htop : q₁.hom.hom ≫ toUnit (kernel q').X = toUnit (kernel (q ≫ q')).X :=
        toUnit_unique _ _
      rw [← htop] at hout
      have hw : q₁.hom.hom ≫ (kernelι q').hom.hom = i₁.hom.hom ≫ q.hom.hom := by
        rw [← Grp.comp_hom_hom, hq₁, Grp.comp_hom_hom]
      exact (IsPullback.of_right hout hw hright).map (Over.forget B)
    have hι : IsClosedSubgroup i₁ := by
      show IsClosedImmersion i₁.hom.hom.left
      exact MorphismProperty.of_isPullback (P := @IsClosedImmersion) hsq inferInstance
    have : Flat q₁.hom.hom.left := MorphismProperty.of_isPullback hsq.flip inferInstance
    have : Surjective q₁.hom.hom.left := MorphismProperty.of_isPullback hsq.flip inferInstance
    have : LocallyOfFinitePresentation q₁.hom.hom.left :=
      MorphismProperty.of_isPullback hsq.flip inferInstance
    have : QuasiCompact q₁.hom.hom.left := MorphismProperty.of_isPullback hsq.flip inferInstance
    have : Smooth q₁.hom.hom.left := MorphismProperty.of_isPullback hsq.flip inferInstance
    have : GeometricallyConnected q₁.hom.hom.left :=
      MorphismProperty.of_isPullback hsq.flip inferInstance
    have hsmooth₁ : Smooth (kernel (q ≫ q')).X.hom := by
      rw [← Over.w q₁.hom.hom]
      infer_instance
    have hconn₁ : ConnectedSpace (kernel (q ≫ q')).X.left :=
      GeometricallyConnected.connectedSpace (f := q₁.hom.hom.left) q₁.hom.hom.left.isOpenMap
    -- the subgroup `N` of the preimage
    let j₁ : N ⟶ kernel (q ≫ q') :=
      pullback.lift j default (by
        apply Grp.hom_ext
        rw [Grp.comp_hom_hom, Grp.comp_hom_hom, Grp.comp_hom_hom, ← Category.assoc, hjq,
          MonObj.one_comp]
        have h1 : (default : N ⟶ Grp.trivial (Over B)).hom.hom = toUnit N.X :=
          toUnit_unique _ _
        rw [h1]
        rfl)
    have hj₁ : j₁ ≫ i₁ = j := pullback.lift_fst _ _ _
    have hj₁c : IsClosedSubgroup j₁ := by
      have : IsClosedImmersion i₁.hom.hom.left := hι
      have : IsClosedImmersion (j₁.hom.hom.left ≫ i₁.hom.hom.left) := by
        change IsClosedImmersion (j₁ ≫ i₁).hom.hom.left
        rw [hj₁]
        exact hj
      exact IsClosedImmersion.of_comp_isClosedImmersion j₁.hom.hom.left i₁.hom.hom.left
    have hker₁ : SubgroupFunctor.range (kernelι q₁) = SubgroupFunctor.range j₁ := by
      apply SubgroupFunctor.ext
      intro T
      ext x
      rw [mem_range_kernelι_iff, SubgroupFunctor.mem_range]
      constructor
      · intro hx
        have hmem : x ≫ i₁.hom.hom ∈ (SubgroupFunctor.range (kernelι q)).carrier T := by
          rw [mem_range_kernelι_iff, Category.assoc, ← Grp.comp_hom_hom, ← hq₁,
            Grp.comp_hom_hom, ← Category.assoc, hx, MonObj.one_comp]
        rw [hker] at hmem
        obtain ⟨y, hy⟩ := hmem
        let y' : T ⟶ N.X := y
        have hy' : y' ≫ j.hom.hom = x ≫ i₁.hom.hom := hy
        refine ⟨y', (cancel_mono i₁.hom.hom).mp ?_⟩
        change (y' ≫ j₁.hom.hom) ≫ i₁.hom.hom = x ≫ i₁.hom.hom
        rw [Category.assoc, ← Grp.comp_hom_hom, hj₁, hy']
      · rintro ⟨y, rfl⟩
        apply (cancel_mono (kernelι q').hom.hom).mp
        rw [MonObj.one_comp, Category.assoc, Category.assoc, ← Grp.comp_hom_hom,
          ← Grp.comp_hom_hom, hq₁, ← Category.assoc, hj₁, Grp.comp_hom_hom,
          hjq, MonObj.comp_one]
    have hseries₁ : HasSplitSeries (m + n) (kernel (q ≫ q')) :=
      ih j₁ q₁ hj₁c inferInstance ⟨inferInstance, inferInstance, inferInstance, hker₁⟩
        (HasSplitSeries.of_iso e hseries')
    show HasSplitSeries ((m + n) + 1) P
    exact ⟨kernel (q ≫ q'), V, i₁, q ≫ q', hι, hsmooth₁, hconn₁, isNormal_range_kernelι _,
      ⟨inferInstanceAs (Flat (q.hom.hom.left ≫ q'.hom.hom.left)),
        inferInstanceAs (Surjective (q.hom.hom.left ≫ q'.hom.hom.left)),
        inferInstanceAs (LocallyOfFinitePresentation (q.hom.hom.left ≫ q'.hom.hom.left)), rfl⟩,
      hvector, hseries₁⟩

/-- **Extension closure of split series over a field.** Over a field, geometric connectedness of
the kernel follows from connectedness, so it suffices that `N` be smooth, quasi-compact and
connected. -/
theorem HasSplitSeries.of_fppfQuotient_of_field {k : Type u} [Field k] {m n : ℕ}
    {N P Q : GroupScheme (Spec (CommRingCat.of k))} [Smooth N.X.hom] [QuasiCompact N.X.hom]
    [ConnectedSpace N.X.left] (hN : HasSplitSeries m N) (j : N ⟶ P) (q : P ⟶ Q)
    (hj : IsClosedSubgroup j) (hqc : QuasiCompact q.hom.hom.left)
    (hq : IsFppfQuotient (SubgroupFunctor.range j) q) (hQ : HasSplitSeries n Q) :
    HasSplitSeries (m + n) P := by
  have : GeometricallyConnected N.X.hom := geometricallyConnected_of_connected N
  exact hN.of_fppfQuotient n j q hj hqc hq hQ

end Extension

end Langlands.GroupScheme.RelativeRoot
