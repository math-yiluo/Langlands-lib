import Langlands.GroupScheme.CentralIsogeny.FpqcReflection
import Langlands.GroupScheme.Reductive.Basic
import Langlands.GroupScheme.OrbitMapFlatProof
import Langlands.AlgebraicGeometry.SmoothReducedProof
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-! # Projections of closed subgroups of fibre-compatible products

A closed subgroup `D` of `C × H` whose two projections agree after composing with
`π : C ⟶ G` and a central isogeny `q : H ⟶ G` maps finitely to `C`; once that projection is
dominant it is a central isogeny. Flatness comes from the orbit-map flatness theorem over an
algebraic closure, descended along the fpqc base change. -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section Flat

set_option backward.isDefEq.respectTransparency false in
/-- Over an algebraically closed field, a surjective homomorphism from a quasi-compact group
locally of finite type onto a reduced group locally of finite type is flat. It is the orbit
map through the identity of the source acting on the target by left translation, and
surjectivity makes this action transitive on rational points. -/
theorem flat_of_surjective_algClosed {K : Type u} [Field K] [IsAlgClosed K]
    {D C : GroupScheme (Spec (CommRingCat.of K))}
    [LocallyOfFiniteType D.X.hom] [QuasiCompact D.X.hom]
    [IsReduced C.X.left] [LocallyOfFiniteType C.X.hom]
    (f : D ⟶ C) [Surjective f.hom.hom.left] : Flat f.hom.hom.left := by
  let a : SchemeAction D C.X := SchemeAction.restrict (ModObj.regular C.X) f
  have hact : ∀ {T : Over (Spec (CommRingCat.of K))} (g : T ⟶ D.X),
      a.act g 1 = g ≫ f.hom.hom := by
    intro T g
    rw [SchemeAction.restrict_act]
    change (g ≫ f.hom.hom) * 1 = g ≫ f.hom.hom
    exact mul_one _
  have htrans : ∀ y : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ C.X,
      ∃ g : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ D.X, a.act g 1 = y := by
    intro y
    have : JacobsonSpace D.X.left := LocallyOfFiniteType.jacobsonSpace D.X.hom
    have hy : y.left ≫ C.X.hom = 𝟙 _ := Over.w y
    let c := y.left (IsLocalRing.closedPoint K)
    have hc : IsClosed ({c} : Set C.X.left) :=
      ((pointEquivClosedPoint C.X.hom) ⟨y.left, hy⟩).2
    obtain ⟨d, hd⟩ := f.hom.hom.left.surjective c
    obtain ⟨d', hd'f, hd'c⟩ := nonempty_inter_closedPoints
      (Z := f.hom.hom.left ⁻¹' {c}) ⟨d, hd⟩
      (hc.preimage f.hom.hom.left.continuous).isLocallyClosed
    let g : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ D.X :=
      Over.homMk (pointOfClosedPoint D.X.hom d' hd'c) (pointOfClosedPoint_comp D.X.hom d' hd'c)
    refine ⟨g, ?_⟩
    rw [hact]
    apply Over.OverMorphism.ext
    apply ext_of_apply_closedPoint_eq C.X.hom (Over.w (g ≫ f.hom.hom)) hy
    change f.hom.hom.left (pointOfClosedPoint D.X.hom d' hd'c (IsLocalRing.closedPoint K)) = c
    rw [pointOfClosedPoint_apply]
    exact hd'f
  have horb : a.act (𝟙 D.X) (toUnit D.X ≫ 1) = f.hom.hom := by
    rw [MonObj.comp_one, hact, Category.id_comp]
  have h := (orbitMapFaithfullyFlat K D C.X a 1 htrans).1
  rwa [horb] at h

set_option backward.isDefEq.respectTransparency false in
/-- Over any field, a surjective homomorphism from a quasi-compact group locally of finite
type onto a smooth group is flat: flatness holds after base change to an algebraic closure
and descends along the faithfully flat quasi-compact base change. -/
theorem flat_of_surjective {k : Type u} [Field k]
    {D C : GroupScheme (Spec (CommRingCat.of k))}
    [LocallyOfFiniteType D.X.hom] [QuasiCompact D.X.hom] [Smooth C.X.hom]
    (f : D ⟶ C) [Surjective f.hom.hom.left] : Flat f.hom.hom.left := by
  let e := toAlgebraicClosure k
  let B := GroupScheme.baseChange e
  have hsq : IsPullback (B.map f).hom.hom.left (pullback.fst D.X.hom e)
      (pullback.fst C.X.hom e) f.hom.hom.left :=
    baseChange_map_isPullback e f
  have : Surjective (B.map f).hom.hom.left :=
    MorphismProperty.of_isPullback hsq.flip inferInstance
  have : LocallyOfFiniteType (B.obj D).X.hom := by
    change LocallyOfFiniteType (pullback.snd D.X.hom e)
    infer_instance
  have : QuasiCompact (B.obj D).X.hom := by
    change QuasiCompact (pullback.snd D.X.hom e)
    infer_instance
  have : Smooth (B.obj C).X.hom := by
    change Smooth (pullback.snd C.X.hom e)
    infer_instance
  have : IsReduced (B.obj C).X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
      (AlgebraicClosure k) _ (B.obj C).X.hom
  have hflat : Flat (B.map f).hom.hom.left := flat_of_surjective_algClosed (B.map f)
  have he : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) e := by
    dsimp [e]
    exact ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  let : Surjective e := he.1.1
  let : Flat e := he.1.2
  let : QuasiCompact e := he.2
  apply MorphismProperty.of_isPullback_of_descendsAlong
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hsq ?_ hflat
  exact ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩

end Flat

section Projection

variable {k : Type u} [Field k] {C H G D : GroupScheme (Spec (CommRingCat.of k))}
  {π : C ⟶ G} {q : H ⟶ G}

set_option backward.isDefEq.respectTransparency false in
/-- The projection to `C` of a closed subgroup of `C × H` on which `π` and a finite `q`
agree is finite: it factors through the fibre product `C ×_G H`, whose projection to `C` is
a base change of `q`, and the factorization is finite because its composite with the
monomorphism `C ×_G H ⟶ C × H` is the closed immersion. -/
theorem isFinite_fst_of_closedSubgroup (hq : IsFinite q.hom.hom.left) (i : D ⟶ C ⊗ H)
    (hi : IsClosedSubgroup i) (hcomm : i ≫ fst C H ≫ π = i ≫ snd C H ≫ q) :
    IsFinite (i ≫ fst C H).hom.hom.left := by
  have : IsClosedImmersion i.hom.hom.left := hi
  have hc : i.hom.hom.left ≫ pullback.fst C.X.hom H.X.hom ≫ π.hom.hom.left =
      i.hom.hom.left ≫ pullback.snd C.X.hom H.X.hom ≫ q.hom.hom.left :=
    congrArg (fun φ : D ⟶ G => φ.hom.hom.left) hcomm
  let φ : D.X.left ⟶ pullback π.hom.hom.left q.hom.hom.left :=
    pullback.lift (i.hom.hom.left ≫ pullback.fst C.X.hom H.X.hom)
      (i.hom.hom.left ≫ pullback.snd C.X.hom H.X.hom) (by simpa only [Category.assoc] using hc)
  let g : pullback π.hom.hom.left q.hom.hom.left ⟶ pullback C.X.hom H.X.hom :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _) (by
      rw [← Over.w π.hom.hom, ← Over.w q.hom.hom, ← Category.assoc, pullback.condition,
        Category.assoc])
  have : Mono g := ⟨fun a b h => pullback.hom_ext
    (by simpa [g] using h =≫ pullback.fst C.X.hom H.X.hom)
    (by simpa [g] using h =≫ pullback.snd C.X.hom H.X.hom)⟩
  have hφg : φ ≫ g = i.hom.hom.left := by
    apply pullback.hom_ext
    · simp [φ, g]
    · simp [φ, g]
  have : IsFinite (φ ≫ g) := by
    rw [hφg]
    infer_instance
  have : IsFinite φ := IsFinite.of_comp φ g
  have : IsFinite (pullback.fst π.hom.hom.left q.hom.hom.left) :=
    MorphismProperty.of_isPullback
      (IsPullback.of_hasPullback π.hom.hom.left q.hom.hom.left).flip hq
  have hf : (i ≫ fst C H).hom.hom.left = φ ≫ pullback.fst _ _ := by
    rw [pullback.lift_fst]
    rfl
  rw [hf]
  infer_instance

/-- The projection to `C` of a smooth affine closed subgroup of `C × H`, on which `π` and a
central isogeny `q` agree, is a central isogeny onto a smooth `C` once it is dominant.
Finiteness is `isFinite_fst_of_closedSubgroup`; a finite dominant map is surjective; flatness
is `flat_of_surjective`; local finite presentation holds over the noetherian target; and a
point of the kernel has central second coordinate in the kernel of `q`, so it commutes with
every point of `D` inside `C × H`. -/
theorem isCentralIsogeny_fst_of_closedSubgroup (hq : IsCentralIsogeny q)
    (hC : Smooth C.X.hom) (i : D ⟶ C ⊗ H) (hi : IsClosedSubgroup i)
    (hcomm : i ≫ fst C H ≫ π = i ≫ snd C H ≫ q)
    (hDs : Smooth D.X.hom) (hDa : IsAffineHom D.X.hom)
    (hdom : IsDominant (i ≫ fst C H).hom.hom.left) :
    IsCentralIsogeny (i ≫ fst C H) := by
  have hfin : IsFinite (i ≫ fst C H).hom.hom.left :=
    isFinite_fst_of_closedSubgroup hq.isFinite i hi hcomm
  have hsurj : Surjective (i ≫ fst C H).hom.hom.left :=
    surjective_of_isDominant_of_isClosed_range _
      (i ≫ fst C H).hom.hom.left.isClosedMap.isClosed_range
  have : LocallyOfFiniteType (i ≫ fst C H).hom.hom.left := by
    have : LocallyOfFiniteType ((i ≫ fst C H).hom.hom.left ≫ C.X.hom) := by
      rw [Over.w]
      infer_instance
    exact locallyOfFiniteType_of_comp _ C.X.hom
  have : IsLocallyNoetherian C.X.left := LocallyOfFiniteType.isLocallyNoetherian C.X.hom
  have hlfp : LocallyOfFinitePresentation (i ≫ fst C H).hom.hom.left :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  have hflat : Flat (i ≫ fst C H).hom.hom.left := flat_of_surjective (i ≫ fst C H)
  refine ⟨⟨hfin, hflat, hsurj⟩, hlfp, ?_⟩
  apply (isCentral_kernelι_iff _).mpr
  intro T x hx
  rw [mem_center]
  intro T' a y
  have : IsClosedImmersion i.hom.hom.left := hi
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  let p₁ := (i ≫ fst C H).hom.hom
  let p₂ := (i ≫ snd C H).hom.hom
  have key : ∀ u v : T' ⟶ D.X, u ≫ p₁ = v ≫ p₁ → u ≫ p₂ = v ≫ p₂ → u = v := by
    intro u v h₁ h₂
    apply (cancel_mono i.hom.hom).mp
    apply CartesianMonoidalCategory.hom_ext
    · simpa only [p₁, Grp.comp_hom_hom, Grp.fst_hom_hom, Category.assoc] using h₁
    · simpa only [p₂, Grp.comp_hom_hom, Grp.snd_hom_hom, Category.assoc] using h₂
  have hcomm' : p₂ ≫ q.hom.hom = p₁ ≫ π.hom.hom := by
    simpa only [p₁, p₂, Grp.comp_hom_hom, Category.assoc] using
      (congrArg (fun φ : D ⟶ G => φ.hom.hom) hcomm).symm
  have hu1 : (a ≫ x) ≫ p₁ = 1 := by
    rw [Category.assoc, hx, MonObj.comp_one]
  have hu2 : ((a ≫ x) ≫ p₂) ≫ q.hom.hom = 1 := by
    rw [Category.assoc, hcomm', ← Category.assoc, hu1, MonObj.one_comp]
  have hz := mem_center.mp (hq.mem_center_of_comp_eq_one hu2) T' (𝟙 T') (y ≫ p₂)
  rw [Category.id_comp] at hz
  change (a ≫ x) * y = y * (a ≫ x)
  refine key _ _ ?_ ?_
  · rw [MonObj.mul_comp, MonObj.mul_comp, hu1, one_mul, mul_one]
  · rw [MonObj.mul_comp, MonObj.mul_comp]
    exact hz.eq

/-- The symmetric statement for the projection to `H`, obtained by swapping the factors. -/
theorem isCentralIsogeny_snd_of_closedSubgroup (hπ : IsCentralIsogeny π)
    (hH : Smooth H.X.hom) (i : D ⟶ C ⊗ H) (hi : IsClosedSubgroup i)
    (hcomm : i ≫ fst C H ≫ π = i ≫ snd C H ≫ q)
    (hDs : Smooth D.X.hom) (hDa : IsAffineHom D.X.hom)
    (hdom : IsDominant (i ≫ snd C H).hom.hom.left) :
    IsCentralIsogeny (i ≫ snd C H) := by
  let s : C ⊗ H ⟶ H ⊗ C := lift (snd C H) (fst C H)
  have : IsIso s := ⟨⟨lift (snd H C) (fst H C), by ext <;> simp [s], by ext <;> simp [s]⟩⟩
  have : IsIso s.hom.hom := (Grp.forget (Over (Spec (CommRingCat.of k)))).map_isIso s
  have : IsIso s.hom.hom.left := (Over.forget (Spec (CommRingCat.of k))).map_isIso s.hom.hom
  have hs₁ : (i ≫ s) ≫ fst H C = i ≫ snd C H := by
    rw [Category.assoc, lift_fst]
  have hs₂ : (i ≫ s) ≫ snd H C = i ≫ fst C H := by
    rw [Category.assoc, lift_snd]
  have : IsClosedImmersion i.hom.hom.left := hi
  have hi' : IsClosedSubgroup (i ≫ s) := by
    change IsClosedImmersion (i.hom.hom.left ≫ s.hom.hom.left)
    infer_instance
  have hcomm' : (i ≫ s) ≫ fst H C ≫ q = (i ≫ s) ≫ snd H C ≫ π := by
    rw [← Category.assoc, hs₁, ← Category.assoc, hs₂, Category.assoc, Category.assoc, hcomm]
  have hdom' : IsDominant ((i ≫ s) ≫ fst H C).hom.hom.left := by
    rw [hs₁]
    exact hdom
  have h := isCentralIsogeny_fst_of_closedSubgroup hπ hH (i ≫ s) hi' hcomm' hDs hDa hdom'
  rwa [hs₁] at h

end Projection

end Langlands.GroupScheme
