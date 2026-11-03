import Langlands.GroupScheme.Rational.ClosedImmersionPullbackProof
import Langlands.GroupScheme.IdentityComponentAction
import Langlands.GroupScheme.Lie.TorusCentralizer
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-! # Invariant augmentation functions detect connected components -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.CoordinateWeights

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G K : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [IsAffineHom K.X.hom]

/-- The actual augmentation has no nonzero invariant function. -/
def HasTrivialInvariantAugmentation (b : AutomorphicAction S.toGrp G) : Prop :=
  0 ∉ support b

/-- Closed affine subgroup membership is vanishing of its actual coordinate
kernel, on every coefficient algebra. -/
theorem mem_range_iff_coordinates_ker
    (j : K ⟶ G) (hsurj : Function.Surjective (pullback j.hom.hom))
    {A : Type u} [CommRing A] [Algebra k A] (g : Lie.AffinePoints G A) :
    g ∈ (SubgroupFunctor.range j).carrier _ ↔
      RingHom.ker (pullback j.hom.hom).toRingHom ≤
        RingHom.ker (Lie.pointCoordinates G g).toRingHom := by
  change (∃ y : Lie.AffinePoints K A, y ≫ j.hom.hom = g) ↔ _
  constructor
  · rintro ⟨y, rfl⟩ x hx
    rw [RingHom.mem_ker] at hx ⊢
    change Lie.pointCoordinates G (y ≫ j.hom.hom) x = 0
    change pullback j.hom.hom x = 0 at hx
    rw [coordinates_comp, AlgHom.comp_apply, hx, map_zero]
  · intro h
    let f := AlgHom.liftOfSurjective (pullback j.hom.hom) hsurj
      (Lie.pointCoordinates G g) h
    refine ⟨(Lie.pointCoordinates K).symm f, ?_⟩
    apply (Lie.pointCoordinates G).injective
    rw [coordinates_comp, Equiv.apply_symm_apply]
    exact AlgHom.liftOfSurjective_comp _ _ _ _

/-- A principal subgroup kernel is tested by one function on every algebra. -/
theorem mem_range_iff_coordinates_eq_zero
    (j : K ⟶ G) (hsurj : Function.Surjective (pullback j.hom.hom))
    {e : CharacterUnits.Coord G}
    (hker : RingHom.ker (pullback j.hom.hom).toRingHom = Ideal.span {e})
    {A : Type u} [CommRing A] [Algebra k A] (g : Lie.AffinePoints G A) :
    g ∈ (SubgroupFunctor.range j).carrier _ ↔ Lie.pointCoordinates G g e = 0 := by
  rw [mem_range_iff_coordinates_ker j hsurj g, hker, Ideal.span_le,
    Set.singleton_subset_iff]
  rfl

omit [IsAffineHom K.X.hom] in
/-- Equality of principal ideals determines their idempotent generators. -/
theorem idempotent_eq_of_span_eq {A : Type*} [CommRing A] {e f : A}
    (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
    (h : Ideal.span {e} = Ideal.span {f}) : e = f := by
  have he' : e ∈ Ideal.span {f} := h ▸ Ideal.subset_span (Set.mem_singleton e)
  have hf' : f ∈ Ideal.span {e} := h.symm ▸ Ideal.subset_span (Set.mem_singleton f)
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp he'
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp hf'
  have hef : e * f = e := by
    rw [ha]
    calc f * a * f = f * f * a := by ring
      _ = f * a := by rw [hf.eq]
  have hfe : f * e = f := by
    rw [hb]
    calc e * b * e = e * e * b := by ring
      _ = e * b := by rw [he.eq]
  exact hef.symm.trans ((mul_comm _ _).trans hfe)

omit [IsAffineHom K.X.hom] in
/-- Stability of the zero locus forces an idempotent to be invariant under the
actual action after every coefficient extension. -/
theorem isEigenfunction_zero_of_stable_zero_locus
    (b : AutomorphicAction S.toGrp G) {e : CharacterUnits.Coord G}
    (he : IsIdempotentElem e)
    (hstable : ∀ (A : Type u) [CommRing A] [Algebra k A]
      (s : Lie.AffinePoints S.toGrp A) (g : Lie.AffinePoints G A),
      Lie.pointCoordinates G g e = 0 → Lie.pointCoordinates G (b.act s g) e = 0) :
    IsEigenfunction b 0 e := by
  have hdiv : ∀ (A : Type u) [CommRing A] [Algebra k A]
      (s : Lie.AffinePoints S.toGrp A) (g : Lie.AffinePoints G A),
      Lie.pointCoordinates G (b.act s g) e ∈
        Ideal.span {Lie.pointCoordinates G g e} := by
    intro A _ _ s g
    let I : Ideal A := Ideal.span {Lie.pointCoordinates G g e}
    let π : A →ₐ[k] A ⧸ I := Ideal.Quotient.mkₐ k I
    have hg : Lie.pointCoordinates G (Lie.affineMap G π g) e = 0 := by
      rw [Lie.pointCoordinates_naturality, AlgHom.comp_apply]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
    have hact := hstable (A ⧸ I) (Lie.affineMap S.toGrp π s) (Lie.affineMap G π g) hg
    rw [← RelativeRoot.act_affineMap, Lie.pointCoordinates_naturality,
      AlgHom.comp_apply] at hact
    exact Ideal.Quotient.eq_zero_iff_mem.mp hact
  intro A _ _ s g
  have h1 := hdiv A s g
  have h2 := hdiv A s⁻¹ (b.act s g)
  rw [← b.act_mul_left, inv_mul_cancel, b.act_one_left] at h2
  have hi : Ideal.span {Lie.pointCoordinates G (b.act s g) e} =
      Ideal.span {Lie.pointCoordinates G g e} :=
    le_antisymm (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr h1))
      (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr h2))
  have heq := idempotent_eq_of_span_eq (he.map (Lie.pointCoordinates G (b.act s g)))
    (he.map (Lie.pointCoordinates G g)) hi
  simpa only [Lie.characterValue_zero, Units.val_one, one_mul] using heq

/-- A stable closed subgroup cut out by an idempotent makes that idempotent
an actual invariant coordinate function. -/
theorem isEigenfunction_zero_of_stable_principal_kernel
    (b : AutomorphicAction S.toGrp G) (j : K ⟶ G)
    (hsurj : Function.Surjective (pullback j.hom.hom))
    (hstable : b.IsStable (SubgroupFunctor.range j))
    {e : CharacterUnits.Coord G} (he : IsIdempotentElem e)
    (hker : RingHom.ker (pullback j.hom.hom).toRingHom = Ideal.span {e}) :
    IsEigenfunction b 0 e := by
  apply isEigenfunction_zero_of_stable_zero_locus b he
  intro A _ _ s g hg
  exact (mem_range_iff_coordinates_eq_zero j hsurj hker _).mp
    (hstable _ s g ((mem_range_iff_coordinates_eq_zero j hsurj hker g).mpr hg))

/-- The kernel of an affine open and closed subgroup is generated by an
idempotent in the actual coordinates. -/
theorem exists_idempotent_kernel_of_isOpenImmersion
    (j : K ⟶ G) (hsurj : Function.Surjective (pullback j.hom.hom))
    (hopen : IsOpenImmersion j.hom.hom.left) :
    ∃ e : CharacterUnits.Coord G, IsIdempotentElem e ∧
      RingHom.ker (pullback j.hom.hom).toRingHom = Ideal.span {e} := by
  have hleft := congrArg CommaMorphism.left
    (PointedCoordinateWeights.algSpec_map_pullback j.hom.hom)
  simp only [Over.comp_left, algSpec_map_left,
    Quiver.Hom.unop_op] at hleft
  let ψ := ((commAlgCatEquivUnder (CommRingCat.of k)).functor.map
    (CommAlgCat.ofHom (pullback j.hom.hom))).right
  change Spec.map ψ ≫ (Lie.coordinateIso G).hom.left =
    (Lie.coordinateIso K).hom.left ≫ j.hom.hom.left at hleft
  have hψ : Spec.map ψ =
      (Lie.coordinateIso K).hom.left ≫ j.hom.hom.left ≫
        (Lie.coordinateIso G).inv.left := by
    rw [← Category.assoc, ← hleft, Category.assoc, ← Over.comp_left,
      Iso.hom_inv_id, Over.id_left]
    change Spec.map ψ = Spec.map ψ ≫ 𝟙 _
    rw [Category.comp_id]
  have : IsOpenImmersion (Spec.map ψ) := by
    rw [hψ]
    infer_instance
  exact (isOpenImmersion_SpecMap_iff_of_surjective ψ hsurj).mp inferInstance

omit [IsAffineHom K.X.hom] in
/-- A smooth affine group with no invariant augmentation function is connected.
The acting group need not be a split torus. -/
theorem connectedSpace_of_trivialInvariantAugmentation
    [Smooth G.X.hom] (b : AutomorphicAction S.toGrp G)
    (h : HasTrivialInvariantAugmentation b) : ConnectedSpace G.X.left := by
  let j : identityComponent G ⟶ G := identityComponentι G
  let φ : CharacterUnits.Coord G →ₐ[k] CharacterUnits.Coord (identityComponent G) :=
    pullback (k := k) (G := identityComponent G) (H := G) j.hom.hom
  have hsurj : Function.Surjective φ := by
    change Function.Surjective (PointedCoordinateWeights.pullback j.hom.hom)
    exact PointedCoordinateWeights.pullback_surjective_of_isClosedImmersion
      j.hom.hom inferInstance
  obtain ⟨e, he, hker⟩ :=
    exists_idempotent_kernel_of_isOpenImmersion (K := identityComponent G)
      j hsurj inferInstance
  have heker : e ∈ RingHom.ker φ.toRingHom := by
    rw [hker]
    exact Ideal.subset_span (Set.mem_singleton _)
  have heres : φ e = 0 := RingHom.mem_ker.mp heker
  have heaug : e ∈ augmentation G := by
    change Lie.coordinateOrigin G e = 0
    rw [← pullback_origin (G := identityComponent G) (H := G) j, AlgHom.comp_apply]
    change Lie.coordinateOrigin (identityComponent G) (φ e) = 0
    rw [heres, map_zero]
  have heinv : IsEigenfunction b 0 e :=
    isEigenfunction_zero_of_stable_principal_kernel (K := identityComponent G) b j hsurj
      b.isStable_range_identityComponentι he hker
  have hezero : e = 0 := by
    by_contra hne
    exact h ⟨⟨e, heaug⟩, fun hzero => hne (congrArg Subtype.val hzero), heinv⟩
  have hinj : Function.Injective φ := by
    apply (RingHom.injective_iff_ker_eq_bot φ.toRingHom).mpr
    rw [hker, hezero, Ideal.span_singleton_eq_bot.mpr rfl]
  let eqv := AlgEquiv.ofBijective φ ⟨hinj, hsurj⟩
  have : IsIso (CommAlgCat.ofHom φ) :=
    (CommAlgCat.isoMk eqv).isIso_hom
  have hj : j.hom.hom = (Lie.coordinateIso (identityComponent G)).inv ≫
      (algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom φ).op ≫
        (Lie.coordinateIso G).hom := by
    have hmap := PointedCoordinateWeights.algSpec_map_pullback j.hom.hom
    change (algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom φ).op ≫
      (Lie.coordinateIso G).hom =
        (Lie.coordinateIso (identityComponent G)).hom ≫ j.hom.hom at hmap
    rw [hmap, Iso.inv_hom_id_assoc]
  have : IsIso j.hom.hom := by rw [hj]; infer_instance
  have : IsIso j.hom.hom.left :=
    inferInstanceAs (IsIso ((Over.forget _).map j.hom.hom))
  exact (Scheme.homeoOfIso (asIso j.hom.hom.left)).connectedSpace_iff.mp inferInstance

end Langlands.GroupScheme.CoordinateWeights
