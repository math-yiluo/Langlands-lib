import Langlands.GroupScheme.IntegralModel.HenselianReduction
import Langlands.AbelianScheme.Kernel
import Langlands.GroupScheme.SchemeActionFiniteTarget

/-! # Containment of a full special-fibre kernel in an open subscheme -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section Field

variable {k : Type u} [Field k]
  {G H : GroupScheme (Spec (CommRingCat.of k))} (q : G ⟶ H)

/-- The kernel of a homomorphism out of a group locally of finite type is again locally of
finite type: the unit section is locally of finite type and the kernel inclusion is its base
change. -/
theorem kernel_locallyOfFiniteType [LocallyOfFiniteType G.X.hom] :
    LocallyOfFiniteType (kernel q).X.hom := by
  have hη : LocallyOfFiniteType η[H.X].left := by
    have he : η[H.X].left ≫ H.X.hom = 𝟙 _ := η[H.X].w
    have : LocallyOfFiniteType (η[H.X].left ≫ H.X.hom) :=
      he.symm ▸ (inferInstance : LocallyOfFiniteType (𝟙 (Spec (CommRingCat.of k))))
    exact locallyOfFiniteType_of_comp η[H.X].left H.X.hom
  have hι : LocallyOfFiniteType (kernelι q).hom.hom.left :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType)
      (kernel_isPullback_scheme q).flip hη
  rw [← Over.w (kernelι q).hom.hom]
  infer_instance

/-- A rational point of the kernel gives a rational point of the source killed by `q`. -/
theorem kernelι_rationalPoint_map (x : rationalPoints (kernel q)) :
    rationalPoints.map q (x ≫ (kernelι q).hom.hom) = 1 :=
  (kernelPointsEquiv q _ x).property

variable [IsAlgClosed k]

/-- **Kernel containment from rational points.** Over an algebraically closed field, if every
rational point of `G` killed by `q` lies in an open set `U`, then the whole scheme-theoretic
kernel of `q` lies in `U`. A point of the kernel outside `U` would give a nonempty closed
subset of the kernel avoiding `U`; by the Jacobson property it contains a closed point, which
is the location of a rational point because the base field is algebraically closed. -/
theorem kernelι_range_subset_of_rationalPoints [LocallyOfFiniteType G.X.hom]
    (U : Set G.X.left) (hU : IsOpen U)
    (h : ∀ p : rationalPoints G, rationalPoints.map q p = 1 →
      p.left (IsLocalRing.closedPoint k) ∈ U) :
    Set.range (kernelι q).hom.hom.left ⊆ U := by
  have : LocallyOfFiniteType (kernel q).X.hom := kernel_locallyOfFiniteType q
  have : JacobsonSpace (kernel q).X.left := LocallyOfFiniteType.jacobsonSpace (kernel q).X.hom
  rintro _ ⟨y, rfl⟩
  by_contra hy
  let Z : Set (kernel q).X.left := (kernelι q).hom.hom.left ⁻¹' Uᶜ
  have hZ : IsClosed Z := hU.isClosed_compl.preimage (kernelι q).hom.hom.left.continuous
  obtain ⟨z, hzZ, hz⟩ := nonempty_inter_closedPoints (Z := Z) ⟨y, hy⟩ hZ.isLocallyClosed
  let x := (rationalPointEquivClosedPoint (kernel q).X).symm ⟨z, hz⟩
  have hxz : x.left (IsLocalRing.closedPoint k) = z :=
    congrArg Subtype.val ((rationalPointEquivClosedPoint (kernel q).X).apply_symm_apply ⟨z, hz⟩)
  have hp := h (x ≫ (kernelι q).hom.hom) (kernelι_rationalPoint_map q x)
  apply hzZ
  rw [Over.comp_left, Scheme.Hom.comp_apply, hxz] at hp
  exact hp

/-- **Kernel factorization through an open immersion.** Over an algebraically closed field, if
every rational point of `G` killed by `q` lies in the range of an open immersion `m`, then the
inclusion of the full scheme-theoretic kernel factors through `m`. -/
theorem exists_kernel_lift_of_rationalPoints [LocallyOfFiniteType G.X.hom]
    {P : Over (Spec (CommRingCat.of k))} (m : P ⟶ G.X) [IsOpenImmersion m.left]
    (h : ∀ p : rationalPoints G, rationalPoints.map q p = 1 →
      p.left (IsLocalRing.closedPoint k) ∈ Set.range m.left) :
    ∃ l : (kernel q).X ⟶ P, l ≫ m = (kernelι q).hom.hom := by
  have hrange := kernelι_range_subset_of_rationalPoints q (Set.range m.left)
    (IsOpenImmersion.isOpen_range m.left) h
  refine ⟨Over.homMk (IsOpenImmersion.lift m.left (kernelι q).hom.hom.left hrange) ?_, ?_⟩
  · rw [← Over.w m, ← Category.assoc, IsOpenImmersion.lift_fac]
    exact Over.w (kernelι q).hom.hom
  · apply Over.OverMorphism.ext
    exact IsOpenImmersion.lift_fac _ _ _

end Field

namespace IntegralModel

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {G H : GroupScheme (Spec (CommRingCat.of K))}

section Local

variable [IsLocalRing R]

/-- The projection from the actual special fibre to the total space of the model. -/
abbrev specialFibreProjection (M : IntegralModel R K G) :
    M.specialFibre.X.left ⟶ M.group.X.left :=
  pullback.fst M.group.X.hom (residueBaseMap R)

omit [IsDomain R] in
/-- The residue base map sends the unique point to the closed point. -/
theorem residueBaseMap_closedPoint :
    residueBaseMap R (IsLocalRing.closedPoint (IsLocalRing.ResidueField R)) =
      IsLocalRing.closedPoint R :=
  IsLocalRing.comap_closedPoint (IsLocalRing.residue R)

/-- The reduction of an integral section has the location of the section's closed point. -/
theorem specialFibreProjection_reduction (M : IntegralModel R K G)
    (x : M.integralSections) :
    M.specialFibreProjection
        ((M.reduction x).left (IsLocalRing.closedPoint (IsLocalRing.ResidueField R))) =
      x.left (IsLocalRing.closedPoint R) := by
  rw [← Scheme.Hom.comp_apply, M.reduction_left]
  change (pullback.lift (residueBaseMap R ≫ x.left) (𝟙 _) _ ≫
      pullback.fst M.group.X.hom (residueBaseMap R)) _ = _
  rw [pullback.lift_fst, Scheme.Hom.comp_apply, residueBaseMap_closedPoint]
  rfl

/-- The base change of an open immersion into the model to the special fibre is again an open
immersion. -/
theorem specialFibre_pullback_map_isOpenImmersion (M : IntegralModel R K G)
    {P : Over (Spec (CommRingCat.of R))} (j : P ⟶ M.group.X) [IsOpenImmersion j.left] :
    IsOpenImmersion ((Over.pullback (residueBaseMap R)).map j).left := by
  have hm : ((Over.pullback (residueBaseMap R)).map j).left =
      pullback.map P.hom (residueBaseMap R) M.group.X.hom (residueBaseMap R) j.left (𝟙 _)
        (𝟙 _) (by rw [Category.comp_id, Over.w j]) (by simp) := by
    change pullback.lift (pullback.fst _ _ ≫ j.left) (pullback.snd _ _) _ = _
    apply pullback.hom_ext <;> simp
  rw [hm]
  infer_instance

end Local

section Henselian

variable [HenselianLocalRing R] [IsAlgClosed (IsLocalRing.ResidueField R)]
  {M : IntegralModel R K G} {N : IntegralModel R K H} {f : G ⟶ H}

/-- **Full special-fibre kernel containment.** Let `R` be a Henselian local domain with
algebraically closed residue field and `φ : M → N` a model morphism with `M` smooth. If every
integral section of `M` whose image in `N` reduces to the identity has its closed point in an
open set `U` of the total space of `M`, then every point of the scheme-theoretic kernel of the
special-fibre map lies over `U`. -/
theorem Hom.specialFibreKernel_subset (φ : M.Hom N f) (hM : M.IsSmooth)
    (U : Set M.group.X.left) (hU : IsOpen U)
    (h : ∀ x : M.integralSections, N.reduction (rationalPoints.map φ.hom x) = 1 →
      x.left (IsLocalRing.closedPoint R) ∈ U)
    (y : (kernel φ.specialFibreMap).X.left) :
    M.specialFibreProjection ((kernelι φ.specialFibreMap).hom.hom.left y) ∈ U := by
  have : LocallyOfFiniteType M.specialFibre.X.hom := by
    change LocallyOfFiniteType (pullback.snd M.group.X.hom (residueBaseMap R))
    infer_instance
  refine kernelι_range_subset_of_rationalPoints φ.specialFibreMap
    (M.specialFibreProjection ⁻¹' U) (hU.preimage M.specialFibreProjection.continuous)
    ?_ ⟨y, rfl⟩
  intro p hp
  obtain ⟨x, rfl⟩ := M.reduction_surjective hM p
  have hx : N.reduction (rationalPoints.map φ.hom x) = 1 := by
    rw [φ.reduction_naturality]
    exact hp
  change M.specialFibreProjection _ ∈ U
  rw [specialFibreProjection_reduction]
  exact h x hx

/-- **Factorization of the full special-fibre kernel through an open chart.** Let `R` be a
Henselian local domain with algebraically closed residue field, `φ : M → N` a model morphism
with `M` smooth, and `j : P → M` a morphism over `Spec R` that is an open immersion. If every
integral section of `M` whose image in `N` reduces to the identity has its closed point in the
range of `j`, then the inclusion of the scheme-theoretic kernel of the special-fibre map factors
through the special fibre of `j`. -/
theorem Hom.exists_specialFibreKernel_lift (φ : M.Hom N f) (hM : M.IsSmooth)
    {P : Over (Spec (CommRingCat.of R))} (j : P ⟶ M.group.X) [IsOpenImmersion j.left]
    (h : ∀ x : M.integralSections, N.reduction (rationalPoints.map φ.hom x) = 1 →
      x.left (IsLocalRing.closedPoint R) ∈ Set.range j.left) :
    ∃ l : (kernel φ.specialFibreMap).X ⟶ (Over.pullback (residueBaseMap R)).obj P,
      l ≫ (Over.pullback (residueBaseMap R)).map j = (kernelι φ.specialFibreMap).hom.hom := by
  have : LocallyOfFiniteType M.specialFibre.X.hom := by
    change LocallyOfFiniteType (pullback.snd M.group.X.hom (residueBaseMap R))
    infer_instance
  have := specialFibre_pullback_map_isOpenImmersion M j
  refine exists_kernel_lift_of_rationalPoints φ.specialFibreMap
    ((Over.pullback (residueBaseMap R)).map j) ?_
  intro p hp
  obtain ⟨x, rfl⟩ := M.reduction_surjective hM p
  have hx : N.reduction (rationalPoints.map φ.hom x) = 1 := by
    rw [φ.reduction_naturality]
    exact hp
  have hrange : Set.range x.left ⊆ Set.range j.left := by
    rintro _ ⟨z, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint z).map x.left.continuous).mem_open
      (IsOpenImmersion.isOpen_range j.left) (h x hx)
  let y := IsOpenImmersion.lift j.left x.left hrange
  have hy : y ≫ j.left = x.left := IsOpenImmersion.lift_fac _ _ _
  have hw : (residueBaseMap R ≫ y) ≫ P.hom = 𝟙 _ ≫ residueBaseMap R := by
    rw [← Over.w j, Category.assoc, ← Category.assoc y, hy, Over.w x]
    simp
  have heq : pullback.lift (residueBaseMap R ≫ y) (𝟙 _) hw ≫
      ((Over.pullback (residueBaseMap R)).map j).left = (M.reduction x).left := by
    rw [M.reduction_left]
    change pullback.lift _ _ _ ≫
      pullback.lift (pullback.fst _ _ ≫ j.left) (pullback.snd _ _) _ = _
    apply pullback.hom_ext
    · simp [hy]
    · simp
  exact ⟨_, (Scheme.Hom.comp_apply _ _ _).symm.trans
    (congrArg (fun g => g (IsLocalRing.closedPoint (IsLocalRing.ResidueField R))) heq)⟩

end Henselian

end IntegralModel
end Langlands.GroupScheme
