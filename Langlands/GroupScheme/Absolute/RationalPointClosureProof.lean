import Langlands.GroupScheme.Absolute.RationalPointClosureStatement
import Langlands.GroupScheme.AffineLinearEmbeddingProof
import Langlands.GroupScheme.CorepresentedSmooth
import Mathlib.AlgebraicGeometry.Group.Smooth

/-! # Proof: the closure of a group of rational points is a smooth closed subgroup -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme

namespace RationalPointClosure

/-- A family of algebra maps `Q → K` that separates the elements of `Q` also separates the
elements of `Q ⊗[K] Q` by the products of pairs of its members. -/
theorem tensor_eq_zero_of_separating {K Q J : Type*} [Field K] [CommRing Q] [Algebra K Q]
    (χ : J → Q →ₐ[K] K) (hχ : ∀ q, (∀ i, χ i q = 0) → q = 0) (t : Q ⊗[K] Q)
    (ht : ∀ i i', Algebra.TensorProduct.lift (χ i) (χ i') (fun _ _ => Commute.all _ _) t = 0) :
    t = 0 := by
  let b := Module.Basis.ofVectorSpace K Q
  obtain ⟨c, rfl⟩ := TensorProduct.eq_repr_basis_left b t
  suffices hc : c = 0 by simp [hc]
  ext a
  rw [Finsupp.coe_zero, Pi.zero_apply]
  apply hχ
  intro i'
  have hd : Finsupp.linearCombination K b (c.mapRange (χ i') (map_zero _)) = 0 := by
    apply hχ
    intro i
    have h := ht i i'
    rw [Finsupp.linearCombination_apply, Finsupp.sum_mapRange_index (h := fun j (x : K) => x • b j)
      (fun _ => zero_smul K _)]
    simp only [Finsupp.sum, map_sum, Algebra.TensorProduct.lift_tmul] at h
    simp only [Finsupp.sum, map_sum, map_smul, smul_eq_mul]
    rw [← h]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  have h0 := (linearIndependent_iff.mp b.linearIndependent) _ hd
  simpa using congrArg (fun f : _ →₀ K => f a) h0

section Core

variable {k : Type u} [Field k] {F : CommAlgCat.{u} (CommRingCat.of k) ⥤ GrpCat.{u}}
  {B : CommAlgCat.{u} (CommRingCat.of k)} (e : (F ⋙ forget GrpCat).CorepresentableBy B)

variable (k) in
/-- The base field `k`, as a commutative algebra over itself. -/
abbrev baseAlgebra : CommAlgCat.{u} (CommRingCat.of k) :=
  CommAlgCat.of (CommRingCat.of k) (CommRingCat.of k)

variable (Γ : Subgroup (F.obj (baseAlgebra k)))

/-- The ideal of the representing algebra of the functions vanishing at every point of `Γ`. -/
def vanishingIdeal : Ideal B :=
  ⨅ x : Γ, RingHom.ker (e.homEquiv.symm x.1).hom

theorem mem_vanishingIdeal {b : B} :
    b ∈ vanishingIdeal e Γ ↔ ∀ x ∈ Γ, (e.homEquiv.symm x).hom b = 0 := by
  simp [vanishingIdeal, RingHom.mem_ker]

theorem homEquiv_symm_map {A A' : CommAlgCat.{u} (CommRingCat.of k)} (f : A ⟶ A')
    (x : F.obj A) : e.homEquiv.symm (F.map f x) = e.homEquiv.symm x ≫ f :=
  (e.homEquiv_symm_comp x f).symm

/-- The points of `F` whose classifying algebra maps kill the vanishing ideal of `Γ`. -/
def cutSet (A : CommAlgCat.{u} (CommRingCat.of k)) : Set (F.obj A) :=
  {x | ∀ b ∈ vanishingIdeal e Γ, (e.homEquiv.symm x).hom b = 0}

variable {e Γ}

theorem map_mem_cutSet {A A' : CommAlgCat.{u} (CommRingCat.of k)} (f : A ⟶ A') {x : F.obj A}
    (hx : x ∈ cutSet e Γ A) : F.map f x ∈ cutSet e Γ A' := by
  intro b hb
  rw [homEquiv_symm_map, CommAlgCat.hom_comp, AlgHom.comp_apply, hx b hb, map_zero]

theorem mem_cutSet_of_mem {x : F.obj (baseAlgebra k)} (hx : x ∈ Γ) :
    x ∈ cutSet e Γ (baseAlgebra k) :=
  fun _ hb => (mem_vanishingIdeal e Γ).1 hb x hx

variable (e Γ)

/-- The quotient of the representing algebra by the vanishing ideal of `Γ`. -/
abbrev quotient : CommAlgCat.{u} (CommRingCat.of k) :=
  Corepresented.quotientAlgebra (vanishingIdeal e Γ)

/-- The point of `F` over the quotient classified by the quotient map. -/
def universalPoint : F.obj (quotient e Γ) :=
  e.homEquiv (Corepresented.quotientMap (vanishingIdeal e Γ))

theorem universalPoint_mem : universalPoint e Γ ∈ cutSet e Γ (quotient e Γ) := by
  intro b hb
  rw [universalPoint, Equiv.symm_apply_apply]
  change Ideal.Quotient.mk _ b = 0
  exact Ideal.Quotient.eq_zero_iff_mem.2 hb

variable {e Γ}

/-- The algebra map out of the quotient classifying a point of `cutSet`. -/
def lift {A : CommAlgCat.{u} (CommRingCat.of k)} (x : F.obj A) (hx : x ∈ cutSet e Γ A) :
    quotient e Γ ⟶ A :=
  CommAlgCat.ofHom (Ideal.Quotient.liftₐ _ (e.homEquiv.symm x).hom hx)

theorem quotientMap_comp_lift {A : CommAlgCat.{u} (CommRingCat.of k)} (x : F.obj A)
    (hx : x ∈ cutSet e Γ A) :
    Corepresented.quotientMap (vanishingIdeal e Γ) ≫ lift x hx = e.homEquiv.symm x := by
  apply CommAlgCat.hom_ext
  rw [CommAlgCat.hom_comp, CommAlgCat.hom_ofHom]
  exact Ideal.Quotient.liftₐ_comp _ _ _

theorem map_lift_universalPoint {A : CommAlgCat.{u} (CommRingCat.of k)} (x : F.obj A)
    (hx : x ∈ cutSet e Γ A) : F.map (lift x hx) (universalPoint e Γ) = x := by
  have h := e.homEquiv_comp (lift x hx) (Corepresented.quotientMap (vanishingIdeal e Γ))
  rw [quotientMap_comp_lift, Equiv.apply_symm_apply] at h
  exact h.symm

theorem mem_cutSet_iff {A : CommAlgCat.{u} (CommRingCat.of k)} (x : F.obj A) :
    x ∈ cutSet e Γ A ↔ ∃ ψ : quotient e Γ ⟶ A, F.map ψ (universalPoint e Γ) = x :=
  ⟨fun hx => ⟨lift x hx, map_lift_universalPoint x hx⟩,
    fun ⟨ψ, h⟩ => h ▸ map_mem_cutSet ψ (universalPoint_mem e Γ)⟩

/-- The points of `Γ` separate the elements of the quotient. -/
theorem eq_zero_of_forall_lift (q : quotient e Γ)
    (hq : ∀ γ : Γ, (lift γ.1 (mem_cutSet_of_mem γ.2)).hom q = 0) : q = 0 := by
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective q
  rw [Ideal.Quotient.eq_zero_iff_mem, mem_vanishingIdeal]
  exact fun x hx => hq ⟨x, hx⟩

/-- A point over `A` lies in `cutSet` as soon as a separating family of `k`-points of `A` maps
it into `Γ`. -/
theorem mem_cutSet_of_separating {A : CommAlgCat.{u} (CommRingCat.of k)} {J : Type*}
    (χ : J → (A ⟶ baseAlgebra k)) (hχ : ∀ a : A, (∀ j, (χ j).hom a = 0) → a = 0)
    {y : F.obj A} (hy : ∀ j, F.map (χ j) y ∈ Γ) : y ∈ cutSet e Γ A := by
  intro b hb
  apply hχ
  intro j
  rw [← AlgHom.comp_apply, ← CommAlgCat.hom_comp, ← homEquiv_symm_map]
  exact (mem_vanishingIdeal e Γ).1 hb _ (hy j)

theorem map_map {A A' A'' : CommAlgCat.{u} (CommRingCat.of k)} (f : A ⟶ A') (g : A' ⟶ A'')
    (x : F.obj A) : F.map g (F.map f x) = F.map (f ≫ g) x := by
  rw [Functor.map_comp]
  rfl

theorem one_mem_cutSet (A : CommAlgCat.{u} (CommRingCat.of k)) : (1 : F.obj A) ∈ cutSet e Γ A := by
  have h := map_mem_cutSet (CommAlgCat.ofHom (Algebra.ofId (CommRingCat.of k) A))
    (mem_cutSet_of_mem (e := e) Γ.one_mem)
  rwa [map_one] at h

theorem inv_mem_cutSet {A : CommAlgCat.{u} (CommRingCat.of k)} {x : F.obj A}
    (hx : x ∈ cutSet e Γ A) : x⁻¹ ∈ cutSet e Γ A := by
  obtain ⟨ψ, rfl⟩ := (mem_cutSet_iff x).1 hx
  have h : F.map ψ (universalPoint e Γ)⁻¹ = (F.map ψ (universalPoint e Γ))⁻¹ := map_inv _ _
  rw [← h]
  refine map_mem_cutSet ψ (mem_cutSet_of_separating
    (fun γ : Γ => lift γ.1 (mem_cutSet_of_mem γ.2)) eq_zero_of_forall_lift fun γ => ?_)
  rw [map_inv, map_lift_universalPoint]
  exact Γ.inv_mem γ.2

variable (e Γ)

/-- The tensor square of the quotient algebra. -/
abbrev tensorSquare : CommAlgCat.{u} (CommRingCat.of k) :=
  CommAlgCat.of (CommRingCat.of k) (quotient e Γ ⊗[CommRingCat.of k] quotient e Γ)

/-- The left inclusion of the quotient into its tensor square. -/
abbrev inclLeft : quotient e Γ ⟶ tensorSquare e Γ :=
  CommAlgCat.ofHom Algebra.TensorProduct.includeLeft

/-- The right inclusion of the quotient into its tensor square. -/
abbrev inclRight : quotient e Γ ⟶ tensorSquare e Γ :=
  CommAlgCat.ofHom Algebra.TensorProduct.includeRight

/-- The product of the two pullbacks of the universal point to the tensor square. -/
def productPoint : F.obj (tensorSquare e Γ) :=
  F.map (inclLeft e Γ) (universalPoint e Γ) * F.map (inclRight e Γ) (universalPoint e Γ)

variable {e Γ}

/-- The `k`-point of the tensor square given by a pair of points of `Γ`. -/
def pairLift (γ : Γ × Γ) : tensorSquare e Γ ⟶ baseAlgebra k :=
  CommAlgCat.ofHom (Algebra.TensorProduct.lift (lift γ.1.1 (mem_cutSet_of_mem γ.1.2)).hom
    (lift γ.2.1 (mem_cutSet_of_mem γ.2.2)).hom fun _ _ => Commute.all _ _)

theorem map_pairLift_productPoint (γ : Γ × Γ) :
    F.map (pairLift γ) (productPoint e Γ) = γ.1.1 * γ.2.1 := by
  rw [productPoint, map_mul, map_map, map_map]
  have hl : inclLeft e Γ ≫ pairLift γ = lift γ.1.1 (mem_cutSet_of_mem γ.1.2) := by
    apply CommAlgCat.hom_ext
    rw [CommAlgCat.hom_comp, pairLift, CommAlgCat.hom_ofHom, CommAlgCat.hom_ofHom]
    exact Algebra.TensorProduct.lift_comp_includeLeft _ _ _
  have hr : inclRight e Γ ≫ pairLift γ = lift γ.2.1 (mem_cutSet_of_mem γ.2.2) := by
    apply CommAlgCat.hom_ext
    rw [CommAlgCat.hom_comp, pairLift, CommAlgCat.hom_ofHom, CommAlgCat.hom_ofHom]
    exact Algebra.TensorProduct.lift_comp_includeRight' _ _ _
  rw [hl, hr, map_lift_universalPoint, map_lift_universalPoint]

theorem productPoint_mem : productPoint e Γ ∈ cutSet e Γ (tensorSquare e Γ) := by
  let : Field (CommRingCat.of k) := inferInstanceAs (Field k)
  refine mem_cutSet_of_separating pairLift (fun t ht => ?_) fun γ => ?_
  · exact tensor_eq_zero_of_separating (fun γ : Γ => (lift γ.1 (mem_cutSet_of_mem γ.2)).hom)
      eq_zero_of_forall_lift t fun γ γ' => ht (γ, γ')
  · rw [map_pairLift_productPoint]
    exact Γ.mul_mem γ.1.2 γ.2.2

theorem mul_mem_cutSet {A : CommAlgCat.{u} (CommRingCat.of k)} {x y : F.obj A}
    (hx : x ∈ cutSet e Γ A) (hy : y ∈ cutSet e Γ A) : x * y ∈ cutSet e Γ A := by
  obtain ⟨ψ, rfl⟩ := (mem_cutSet_iff x).1 hx
  obtain ⟨ψ', rfl⟩ := (mem_cutSet_iff y).1 hy
  let L : tensorSquare e Γ ⟶ A := CommAlgCat.ofHom
    (Algebra.TensorProduct.lift ψ.hom ψ'.hom fun _ _ => Commute.all _ _)
  have hl : inclLeft e Γ ≫ L = ψ := by
    apply CommAlgCat.hom_ext
    rw [CommAlgCat.hom_comp, CommAlgCat.hom_ofHom, CommAlgCat.hom_ofHom]
    exact Algebra.TensorProduct.lift_comp_includeLeft _ _ _
  have hr : inclRight e Γ ≫ L = ψ' := by
    apply CommAlgCat.hom_ext
    rw [CommAlgCat.hom_comp, CommAlgCat.hom_ofHom, CommAlgCat.hom_ofHom]
    exact Algebra.TensorProduct.lift_comp_includeRight' _ _ _
  have h : F.map L (productPoint e Γ) = F.map ψ (universalPoint e Γ) *
      F.map ψ' (universalPoint e Γ) := by
    rw [productPoint, map_mul, map_map, map_map, hl, hr]
  rw [← h]
  exact map_mem_cutSet L productPoint_mem

variable (e Γ)

/-- The subgroups of points whose classifying maps kill the vanishing ideal of `Γ`. -/
def closureSubgroup (A : CommAlgCat.{u} (CommRingCat.of k)) : Subgroup (F.obj A) where
  carrier := cutSet e Γ A
  one_mem' := one_mem_cutSet A
  mul_mem' := mul_mem_cutSet
  inv_mem' := inv_mem_cutSet

theorem isCutOutBy_closureSubgroup :
    Corepresented.IsCutOutBy e (closureSubgroup e Γ) (vanishingIdeal e Γ) :=
  fun _ _ => Iff.rfl

/-- The quotient by the vanishing ideal of `Γ` is reduced. -/
theorem isReduced_quotient : IsReduced (quotient e Γ) := by
  let : Field (CommRingCat.of k) := inferInstanceAs (Field k)
  refine ⟨fun q ⟨n, hn⟩ => eq_zero_of_forall_lift q fun γ => ?_⟩
  exact IsNilpotent.eq_zero ⟨n, by rw [← map_pow, hn, map_zero]⟩

end Core

section Geometry

/-- The isomorphism from the coordinate model of `G` to `G` has underlying morphism `j`. -/
theorem modelIso_hom_hom_hom {R : CommRingCat.{u}} (G : GroupScheme (Spec R))
    {B : CommAlgCat.{u} R} (j : (algSpec R).obj (op B) ≅ G.X) :
    (AffineLinearEmbedding.modelIso G j).hom.hom.hom = j.hom := by
  have h : yonedaGrp.map (AffineLinearEmbedding.modelIso G j).hom = _ :=
    (yonedaGrpFullyFaithful (C := Over (Spec R))).map_preimage _
  have h' := congrArg (fun α : yonedaGrp.obj (AffineLinearEmbedding.model G j) ⟶ yonedaGrp.obj G =>
    ConcreteCategory.hom (α.app (op (AffineLinearEmbedding.model G j).X)) (𝟙 _)) h
  refine (Category.id_comp _).symm.trans (h'.trans ?_)
  exact Category.id_comp j.hom

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
open MonObj MonoidalCategory CartesianMonoidalCategory in
/-- A reduced group scheme locally of finite type over an algebraically closed field is smooth.
This is a verbatim copy of the private Mathlib lemma
`AlgebraicGeometry.smooth_of_grpObj_of_isAlgClosed` (Andrew Yang, Apache 2.0). -/
theorem smooth_of_grpObj_of_isAlgClosed {K : Type u} [Field K] {G : Scheme.{u}}
    (f : G ⟶ Spec (.of K)) [LocallyOfFiniteType f] [GrpObj (Over.mk f)] [IsReduced G]
    [IsAlgClosed K] : Smooth f := by
  have := LocallyOfFiniteType.jacobsonSpace f
  have : Nonempty G := ⟨η[Over.mk f].1 (IsLocalRing.closedPoint _)⟩
  rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← TopologicalSpace.Opens.coe_eq_univ,
    ← not_ne_iff, ← Set.nonempty_compl]
  intro H
  obtain ⟨x, hx, hxc⟩ :=
    nonempty_inter_closedPoints H f.smoothLocus.2.isClosed_compl.isLocallyClosed
  obtain ⟨y, hy : y ∈ f.smoothLocus, hyc⟩ := nonempty_inter_closedPoints
    f.dense_smoothLocus_of_perfectField.nonempty f.smoothLocus.2.isLocallyClosed
  let x' : 𝟙_ _ ⟶ Over.mk f := Over.homMk _ ((pointEquivClosedPoint f).symm ⟨x, hxc⟩).2
  let y' : 𝟙_ _ ⟶ Over.mk f := Over.homMk _ ((pointEquivClosedPoint f).symm ⟨y, hyc⟩).2
  let α := (GrpObj.mulRight (A := Over.mk f) x').symm ≪≫
    (GrpObj.mulRight (A := Over.mk f) y')
  have hα : x' ≫ α.hom = y' := by
    dsimp only [Iso.trans_hom, Iso.symm_hom, α]
    rw [← Category.assoc, ← Iso.eq_comp_inv]
    simp [comp_lift_assoc]
  have hα' : α.hom.left x = y := by
    simpa [x', y', pointEquivClosedPoint] using congr(($hα).left (IsLocalRing.closedPoint K))
  rw! [← hα', ← α.hom.left.mem_preimage, Scheme.Hom.preimage_smoothLocus_eq,
    show α.hom.left ≫ f = f from α.hom.w] at hy
  exact hx hy

variable {k : Type u} [Field k]

/-- The point of `Spec B` at which a `k`-point classified by `f : B → k` is located. -/
def classifiedPoint {B : CommAlgCat.{u} (CommRingCat.of k)} (f : B ⟶ baseAlgebra k) :
    PrimeSpectrum B :=
  PrimeSpectrum.comap f.hom.toRingHom (IsLocalRing.closedPoint k)

theorem mem_asIdeal_classifiedPoint {B : CommAlgCat.{u} (CommRingCat.of k)}
    (f : B ⟶ baseAlgebra k) (b : B) : b ∈ (classifiedPoint f).asIdeal ↔ f.hom b = 0 := by
  rw [classifiedPoint, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
  change f.hom b ∈ IsLocalRing.maximalIdeal k ↔ _
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_ne_zero, not_not]

variable {H : GroupScheme (Spec (CommRingCat.of k))} {B : CommAlgCat.{u} (CommRingCat.of k)}
  (j : (algSpec (CommRingCat.of k)).obj (op B) ≅ H.X)

/-- A `k`-point of `H` is located at the image under `j` of the point classified by its
coordinate map. -/
theorem left_classifiedPoint
    (x : (algSpec (CommRingCat.of k)).obj (op (baseAlgebra k)) ⟶ H.X) :
    j.hom.left (classifiedPoint ((AffineLinearEmbedding.corepresentableBy H j).homEquiv.symm x)) =
      x.left (IsLocalRing.closedPoint k) := by
  conv_rhs => rw [← (AffineLinearEmbedding.corepresentableBy H j).homEquiv.apply_symm_apply x]
  rfl

end Geometry

end RationalPointClosure

open RationalPointClosure in
/-- Over an algebraically closed field, the Zariski closure of a group of rational points of an
affine group scheme locally of finite type is the underlying set of a smooth closed subgroup. -/
theorem rationalPointClosureSubgroup : RationalPointClosureSubgroupStatement.{u} := by
  intro k _ _ H _ _ Γ
  have : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  obtain ⟨⟨B⟩, ⟨j⟩⟩ := (essImage_algSpec (G := H.X)).mpr this
  let e := AffineLinearEmbedding.corepresentableBy H j
  let ιso : (algSpec (CommRingCat.of k)).obj (op (baseAlgebra k)) ≅
      Over.mk (𝟙 (Spec (CommRingCat.of k))) :=
    Over.isoMk (Iso.refl _) (by simp; exact Category.id_comp _)
  let Γ' : Subgroup (H.affinePointFunctor.obj (baseAlgebra k)) :=
    Γ.map (H.points.map ιso.hom.op).hom
  have hI := isCutOutBy_closureSubgroup e Γ'
  let ζ := Corepresented.cutHom hI ≫ (AffineLinearEmbedding.modelIso H j).hom
  have hj : IsIso j.hom.left := inferInstanceAs (IsIso ((Over.forget _).map j.hom))
  let c : (Corepresented.cutGroupScheme hI).X.left ⟶
      ((algSpec (CommRingCat.of k)).obj (op B)).left :=
    (Corepresented.cutHom hI).hom.hom.left
  have hc : c = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (vanishingIdeal e Γ'))) :=
    Corepresented.cutHom_left hI
  have hζl : ζ.hom.hom.left = c ≫ j.hom.left := by
    change (Corepresented.cutHom hI).hom.hom.left ≫
      (AffineLinearEmbedding.modelIso H j).hom.hom.hom.left = _
    rw [modelIso_hom_hom_hom]
    rfl
  have hζ : IsClosedImmersion ζ.hom.hom.left := by
    have : IsClosedImmersion c := Corepresented.isClosedImmersion_cutHom hI
    rw [hζl]
    infer_instance
  refine ⟨Corepresented.cutGroupScheme hI, ζ, hζ, ?_, ?_⟩
  · have : _root_.IsReduced (B ⧸ vanishingIdeal e Γ') := isReduced_quotient e Γ'
    have : IsReduced (Corepresented.cutGroupScheme hI).X.left :=
      inferInstanceAs (IsReduced (Spec (CommRingCat.of (B ⧸ vanishingIdeal e Γ'))))
    have : LocallyOfFiniteType (Corepresented.cutGroupScheme hI).X.hom := by
      rw [← Over.w ζ.hom.hom]
      infer_instance
    have : GrpObj (Over.mk (Corepresented.cutGroupScheme hI).X.hom) :=
      inferInstanceAs (GrpObj (Corepresented.cutGroupScheme hI).X)
    exact smooth_of_grpObj_of_isAlgClosed (Corepresented.cutGroupScheme hI).X.hom
  · let S : Set (PrimeSpectrum B) := {p | ∃ x ∈ Γ', p = classifiedPoint (e.homEquiv.symm x)}
    have hS : PrimeSpectrum.vanishingIdeal S = vanishingIdeal e Γ' := by
      ext b
      rw [PrimeSpectrum.mem_vanishingIdeal, mem_vanishingIdeal]
      constructor
      · intro h x hx
        exact (mem_asIdeal_classifiedPoint _ b).1 (h _ ⟨x, hx, rfl⟩)
      · rintro h _ ⟨x, hx, rfl⟩
        exact (mem_asIdeal_classifiedPoint _ b).2 (h x hx)
    have hcut : Set.range c = closure S := by
      rw [hc, ← PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, hS]
      have h := range_comap_of_surjective _ (Ideal.Quotient.mk (vanishingIdeal e Γ'))
        Ideal.Quotient.mk_surjective
      rw [Ideal.mk_ker] at h
      exact h
    have himage : j.hom.left '' S = rationalPointImage H Γ := by
      ext y
      constructor
      · rintro ⟨_, ⟨_, ⟨g, hg, rfl⟩, rfl⟩, rfl⟩
        exact ⟨g, hg, (left_classifiedPoint j ((H.points.map ιso.hom.op).hom g)).symm⟩
      · rintro ⟨g, hg, rfl⟩
        exact ⟨_, ⟨_, ⟨g, hg, rfl⟩, rfl⟩, left_classifiedPoint j _⟩
    rw [hζl]
    calc Set.range (c ≫ j.hom.left)
        = j.hom.left '' Set.range c := Set.range_comp (fun x => j.hom.left x) (fun x => c x)
      _ = j.hom.left '' closure S := by rw [hcut]; rfl
      _ = closure (j.hom.left '' S) := j.hom.left.homeomorph.image_closure S
      _ = closure (rationalPointImage H Γ) := by rw [himage]

end Langlands.GroupScheme
