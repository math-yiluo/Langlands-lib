import Langlands.Global.Arithmetic.HarrisProposition48StabilizerComparison
import Langlands.ClassField.Global.CompletionTower

/-! # Descent from the completion at the auxiliary place -/

noncomputable section

universe uF u

namespace Langlands.Global.Harris

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open AdelicFunctoriality GeneralPosition LocalFactor.CommonClosure
open Langlands.ClassField.Global Langlands.ClassField.Global.FundamentalClass
open scoped NumberField FiniteExtension

namespace MackeyCompletion

section Tower

variable {E E' L : Type u} [Field E] [NumberField E] [Field E'] [NumberField E']
  [Field L] [NumberField L] [Algebra E E'] [Algebra E L] [Algebra E' L] [IsScalarTower E E' L]

/-- When a base place has a single extension to the top, the same holds from any
place of an intermediate field up to the top. -/
theorem uniqueAboveMiddle {v : FinitePlace E} (h : HasUniquePlaceAbove L v)
    (v' : FinitePlace E') [v'.asIdeal.LiesOver v.asIdeal] : HasUniquePlaceAbove L v' := by
  intro w w' hw hw'
  exact h w w' (Ideal.LiesOver.trans w.asIdeal v'.asIdeal v.asIdeal)
    (Ideal.LiesOver.trans w'.asIdeal v'.asIdeal v.asIdeal)

/-- The same uniqueness holds for the extension to the intermediate field. -/
theorem uniqueAboveBase {v : FinitePlace E} (h : HasUniquePlaceAbove L v) :
    HasUniquePlaceAbove E' v := by
  let : Subsingleton (FinitePlacesAbove E' v) := finitePlacesAbove_subsingleton v h
  intro w w' hw hw'
  exact congrArg Subtype.val (Subsingleton.elim (⟨w, hw⟩ : FinitePlacesAbove E' v) ⟨w', hw'⟩)

end Tower

section Fields

variable {E L : Type u} [Field E] [NumberField E] [Field L] [NumberField L] [Algebra E L]

/-- At a place with a single extension, the local degree is the global degree. -/
theorem finrank_eq (v : FinitePlace E) (w : FinitePlace L) [hw : w.asIdeal.LiesOver v.asIdeal]
    (h : HasUniquePlaceAbove L v) :
    Module.finrank (v.adicCompletion E) (w.adicCompletion L) = Module.finrank E L := by
  classical
  let : Unique (FinitePlacesAbove L v) :=
    { default := ⟨w, hw⟩
      uniq r := Subtype.ext (h r.1 w r.2 hw) }
  have hdeg := finiteLocalDegree_sum (L := L) v
  rw [Fintype.sum_unique] at hdeg
  exact hdeg

variable [IsGalois E L] (v : FinitePlace E) (w : FinitePlace L) [hw : w.asIdeal.LiesOver v.asIdeal]

/-- With a unique place above `v`, the decomposition group is all of `Gal(L/E)`. -/
def autEquiv (h : HasUniquePlaceAbove L v) :
    (w.adicCompletion L ≃ₐ[v.adicCompletion E] w.adicCompletion L) ≃* (L ≃ₐ[E] L) :=
  MulEquiv.ofBijective (decompositionHom v w)
    ⟨decompositionHom_injective v w, fun a => (mem_range_decompositionHom_iff v w a).mpr <| by
      have ha := finitePlaceEquiv_liesOver (RingEquiv.refl E) a.toRingEquiv a.commutes v w
      exact h _ w (by simpa using ha) hw⟩

/-- The correspondence of automorphisms is restriction on the number field. -/
theorem autEquiv_apply (h : HasUniquePlaceAbove L v)
    (s : w.adicCompletion L ≃ₐ[v.adicCompletion E] w.adicCompletion L) (x : L) :
    algebraMap L (w.adicCompletion L) (autEquiv v w h s x) =
      s (algebraMap L (w.adicCompletion L) x) :=
  algebraMap_decompositionHom v w s x

end Fields

section Intermediate

variable {E B L : Type u} [Field E] [NumberField E] [Field B] [NumberField B]
  [Field L] [NumberField L] [Algebra E B] [Algebra E L] [Algebra B L] [IsScalarTower E B L]
  (v : FinitePlace E) (b : FinitePlace B) (w : FinitePlace L)
  [b.asIdeal.LiesOver v.asIdeal] [w.asIdeal.LiesOver b.asIdeal] [w.asIdeal.LiesOver v.asIdeal]

/-- The actual completion of the middle field, as a subfield of the completed top. -/
def image : IntermediateField (v.adicCompletion E) (w.adicCompletion L) :=
  (IsScalarTower.toAlgHom (v.adicCompletion E) (b.adicCompletion B) (w.adicCompletion L)).fieldRange

theorem mem_image_iff (x : w.adicCompletion L) :
    x ∈ image v b w ↔ ∃ y : b.adicCompletion B, FiniteExtension.completionMap b w y = x :=
  Iff.rfl

theorem finrank_image (h : HasUniquePlaceAbove B v) :
    Module.finrank (v.adicCompletion E) (image v b w) = Module.finrank E B := by
  rw [← finrank_eq v b h]
  exact ((IsScalarTower.toAlgHom (v.adicCompletion E) (b.adicCompletion B)
    (w.adicCompletion L)).equivFieldRange.toLinearEquiv.finrank_eq).symm

variable [IsGalois E L]

theorem mem_image_fixingSubgroup_iff (h : HasUniquePlaceAbove L v)
    (s : w.adicCompletion L ≃ₐ[v.adicCompletion E] w.adicCompletion L) :
    s ∈ (image v b w).fixingSubgroup ↔
      ∀ x : B, autEquiv v w h s (algebraMap B L x) = algebraMap B L x := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro hs x
    have hx := hs (FiniteExtension.completionMap b w (algebraMap B (b.adicCompletion B) x))
      ((mem_image_iff v b w _).mpr ⟨_, rfl⟩)
    rw [FiniteExtension.completionMap_coe, ← autEquiv_apply v w h] at hx
    exact (algebraMap L (w.adicCompletion L)).injective hx
  · intro hs y hy
    obtain ⟨z, rfl⟩ := (mem_image_iff v b w y).mp hy
    apply congrFun ((denseRange_algebraMap B b).equalizer
      ((continuous_localAut v w s).comp (FiniteExtension.continuous_completionMap b w))
      (FiniteExtension.continuous_completionMap b w) ?_) z
    funext x
    simp only [Function.comp_apply, FiniteExtension.completionMap_coe,
      ← autEquiv_apply v w h, hs]

end Intermediate

section Correspondence

variable {E L : Type u} [Field E] [NumberField E] [Field L] [NumberField L] [Algebra E L]
  (v : FinitePlace E) (w : FinitePlace L) [hw : w.asIdeal.LiesOver v.asIdeal]

omit [NumberField E] [NumberField L] in
/-- Restricting the top place to an intermediate field gives a place above the base. -/
theorem under_liesOver (B : IntermediateField E L) :
    (w.under (𝓞 B)).asIdeal.LiesOver v.asIdeal := by
  constructor
  change v.asIdeal = (w.asIdeal.under (𝓞 B)).under (𝓞 E)
  rw [Ideal.under_under]
  exact hw.over

/-- The image in the top completion of a global intermediate field completed at
the restriction of the top place. -/
def completedField (B : IntermediateField E L) :
    IntermediateField (v.adicCompletion E) (w.adicCompletion L) :=
  letI := under_liesOver v w B
  image v (w.under (𝓞 B)) w

variable [IsGalois E L] (h : HasUniquePlaceAbove L v)

theorem fixingSubgroup_completedField (B : IntermediateField E L) :
    (completedField v w B).fixingSubgroup =
      B.fixingSubgroup.comap (autEquiv v w h).toMonoidHom := by
  let := under_liesOver v w B
  ext s
  rw [Subgroup.mem_comap, IntermediateField.mem_fixingSubgroup_iff (K := B)]
  exact (mem_image_fixingSubgroup_iff v (w.under (𝓞 B)) w h s).trans Subtype.forall

/-- Every completed intermediate field comes from the global field fixed by its
transported fixing subgroup. -/
theorem completedField_fixedField
    (S : IntermediateField (v.adicCompletion E) (w.adicCompletion L)) :
    completedField v w
      (IntermediateField.fixedField (S.fixingSubgroup.map (autEquiv v w h).toMonoidHom)) = S := by
  have := isGalois_adicCompletion v w
  apply IsGalois.intermediateFieldEquivSubgroup.injective
  change (completedField v w _).fixingSubgroup = S.fixingSubgroup
  rw [fixingSubgroup_completedField v w h, IntermediateField.fixingSubgroup_fixedField]
  exact Subgroup.comap_map_eq_self_of_injective
    (f := (autEquiv v w h).toMonoidHom) (autEquiv v w h).injective _

include h in
theorem completedField_le_iff (B C : IntermediateField E L) :
    completedField v w B ≤ completedField v w C ↔ B ≤ C := by
  have := isGalois_adicCompletion v w
  rw [← IsGalois.intermediateFieldEquivSubgroup.le_iff_le,
    ← IsGalois.intermediateFieldEquivSubgroup.le_iff_le (x := B) (y := C)]
  change (completedField v w C).fixingSubgroup ≤ (completedField v w B).fixingSubgroup ↔
    C.fixingSubgroup ≤ B.fixingSubgroup
  rw [fixingSubgroup_completedField v w h, fixingSubgroup_completedField v w h]
  exact Subgroup.comap_le_comap_of_surjective
    (f := (autEquiv v w h).toMonoidHom) (autEquiv v w h).surjective

/-- Completion at the unique extended place gives an order isomorphism of
intermediate fields. -/
def intermediateFieldEquiv :
    IntermediateField E L ≃o IntermediateField (v.adicCompletion E) (w.adicCompletion L) :=
  OrderIso.ofSurjective (OrderEmbedding.ofMapLEIff (completedField v w)
    (completedField_le_iff v w h))
    (fun S => ⟨_, completedField_fixedField v w h S⟩)

include h in
/-- Galois subextensions are preserved and reflected by completion. -/
theorem isGalois_completedField_iff (B : IntermediateField E L) :
    IsGalois (v.adicCompletion E) (completedField v w B) ↔ IsGalois E B := by
  let := isGalois_adicCompletion v w
  have hnormal : (completedField v w B).fixingSubgroup.Normal ↔
      B.fixingSubgroup.Normal := by
    rw [fixingSubgroup_completedField v w h]
    exact Subgroup.normal_comap_iff_of_surjective (autEquiv v w h).surjective
  constructor
  · intro hB
    have : B.fixingSubgroup.Normal := hnormal.mp inferInstance
    rw [← IsGalois.fixedField_fixingSubgroup B]
    infer_instance
  · intro hB
    have : (completedField v w B).fixingSubgroup.Normal := hnormal.mpr inferInstance
    rw [← IsGalois.fixedField_fixingSubgroup (completedField v w B)]
    infer_instance

include h in
/-- Completion at the unique extended place commutes with normal closure in a
finite Galois ambient extension. -/
theorem completedField_normalClosure (B : IntermediateField E L) :
    completedField v w (IntermediateField.normalClosure E B L) =
      IntermediateField.normalClosure (v.adicCompletion E) (completedField v w B)
        (w.adicCompletion L) := by
  let := isGalois_adicCompletion v w
  let S := IntermediateField.normalClosure (v.adicCompletion E) (completedField v w B)
    (w.adicCompletion L)
  let C := (intermediateFieldEquiv v w h).symm S
  have hC : completedField v w C = S := (intermediateFieldEquiv v w h).apply_symm_apply S
  have : IsGalois (v.adicCompletion E) S := IsGalois.normalClosure _ _ _
  have : IsGalois E C := (isGalois_completedField_iff v w h C).mp (by rw [hC]; infer_instance)
  have : IsGalois (v.adicCompletion E)
      (completedField v w (IntermediateField.normalClosure E B L)) :=
    (isGalois_completedField_iff v w h _).mpr inferInstance
  change completedField v w (IntermediateField.normalClosure E B L) = S
  apply le_antisymm
  · rw [← hC, completedField_le_iff v w h, IntermediateField.normalClosure_le_iff_of_normal,
      ← completedField_le_iff v w h, hC]
    exact IntermediateField.le_normalClosure _
  · rw [IntermediateField.normalClosure_le_iff_of_normal, completedField_le_iff v w h]
    exact IntermediateField.le_normalClosure _

omit [IsGalois E L] in
include h in
theorem finrank_completedField (B : IntermediateField E L) :
    Module.finrank (v.adicCompletion E) (completedField v w B) = Module.finrank E B := by
  let := under_liesOver v w B
  exact finrank_image v (w.under (𝓞 B)) w (uniqueAboveBase h)

include h in
/-- A prime Galois step of the local tower descends to a prime cyclic global step. -/
theorem exists_primeCyclic_completedField
    (S : IntermediateField (v.adicCompletion E) (w.adicCompletion L))
    [IsGalois (v.adicCompletion E) S]
    (hp : (Module.finrank (v.adicCompletion E) S).Prime) :
    ∃ B : IntermediateField E L, completedField v w B = S ∧
      IsGalois E B ∧ IsCyclic (B ≃ₐ[E] B) ∧ (Module.finrank E B).Prime := by
  have := isGalois_adicCompletion v w
  let H := S.fixingSubgroup.map (autEquiv v w h).toMonoidHom
  let : H.Normal := (MulEquiv.normal_map_iff (f := autEquiv v w h)).mpr inferInstance
  let B := IntermediateField.fixedField H
  have hB : completedField v w B = S := completedField_fixedField v w h S
  have hpB : (Module.finrank E B).Prime := by
    rw [← finrank_completedField v w h B, hB]
    exact hp
  let : Fact (Module.finrank E B).Prime := ⟨hpB⟩
  exact ⟨B, hB, inferInstance, isCyclic_of_prime_card (IsGalois.card_aut_eq_finrank E B), hpB⟩

end Correspondence

section Transport

variable {K M K' M' : Type*} [Field K] [Field M] [Field K'] [Field M']
  [Algebra K M] [Algebra K' M'] (e : K ≃+* K') (f : M ≃+* M')
  (comm : ∀ x : K, f (algebraMap K M x) = algebraMap K' M' (e x))

/-- Pull an intermediate field back through a commuting square of field isomorphisms. -/
def pullback (S : IntermediateField K' M') : IntermediateField K M where
  __ := S.toSubfield.comap f.toRingHom
  algebraMap_mem' x := by
    change f (algebraMap K M x) ∈ S
    rw [comm]
    exact S.algebraMap_mem _

@[simp]
theorem mem_pullback (S : IntermediateField K' M') (x : M) :
    x ∈ pullback e f comm S ↔ f x ∈ S :=
  Iff.rfl

/-- The pulled back field is isomorphic to its image in the commuting square. -/
def pullbackEquiv (S : IntermediateField K' M') : pullback e f comm S ≃+* S where
  toFun x := ⟨f x, x.2⟩
  invFun y := ⟨f.symm y, by simpa only [mem_pullback, f.apply_symm_apply] using y.2⟩
  left_inv x := Subtype.ext (f.symm_apply_apply x)
  right_inv y := Subtype.ext (f.apply_symm_apply y)
  map_mul' x y := Subtype.ext (f.map_mul x y)
  map_add' x y := Subtype.ext (f.map_add x y)

theorem pullbackEquiv_commutes (S : IntermediateField K' M') (x : K) :
    pullbackEquiv e f comm S (algebraMap K (pullback e f comm S) x) =
      algebraMap K' S (e x) :=
  Subtype.ext (comm x)

end Transport

section ImageTransport

variable {K M K' M' : Type*} [Field K] [Field M] [Field K'] [Field M']
  [Algebra K M] [Algebra K' M'] (e : K ≃+* K') (f : M →+* M')
  (comm : ∀ x : K, f (algebraMap K M x) = algebraMap K' M' (e x))

/-- The image of an intermediate field under an embedding over an isomorphism of bases. -/
def mapField (S : IntermediateField K M) : IntermediateField K' M' where
  __ := S.toSubfield.map f
  algebraMap_mem' x := by
    obtain ⟨y, rfl⟩ := e.surjective x
    exact ⟨algebraMap K M y, S.algebraMap_mem y, comm y⟩

theorem mem_mapField (S : IntermediateField K M) (x : M') :
    x ∈ mapField e f comm S ↔ ∃ y ∈ S, f y = x :=
  Iff.rfl

/-- The source subfield is canonically isomorphic to that image. -/
def mapFieldEquiv (S : IntermediateField K M) : S ≃+* mapField e f comm S :=
  RingEquiv.ofBijective ((f.comp S.val.toRingHom).codRestrict (mapField e f comm S)
    (fun x => ⟨x, x.2, rfl⟩)) (by
      constructor
      · intro x y h
        exact Subtype.ext (f.injective (congrArg Subtype.val h))
      · intro x
        obtain ⟨y, hy, hxy⟩ := (mem_mapField e f comm S x).mp x.2
        exact ⟨⟨y, hy⟩, Subtype.ext hxy⟩)

@[simp]
theorem coe_mapFieldEquiv (S : IntermediateField K M) (x : S) :
    (mapFieldEquiv e f comm S x : M') = f x :=
  rfl

theorem mapFieldEquiv_commutes (S : IntermediateField K M) :
    (algebraMap K' (mapField e f comm S)).comp e.toRingHom =
      (mapFieldEquiv e f comm S).toRingHom.comp (algebraMap K S) :=
  RingHom.ext fun x => Subtype.ext (comm x).symm

theorem mapField_mono : Monotone (mapField e f comm) := by
  intro S T h x hx
  obtain ⟨y, hy, rfl⟩ := (mem_mapField e f comm S x).mp hx
  exact ⟨y, h hy, rfl⟩

theorem normal_mapField_iff (S : IntermediateField K M) :
    Normal K' (mapField e f comm S) ↔ Normal K S := by
  constructor
  · intro h
    let he := mapFieldEquiv e f comm S
    refine Normal.of_equiv_equiv (f := e.symm) (g := he.symm) (RingHom.ext fun x => ?_)
    obtain ⟨y, rfl⟩ := e.surjective x
    apply he.injective
    change he (algebraMap K S (e.symm (e y))) =
      he (he.symm (algebraMap K' (mapField e f comm S) (e y)))
    rw [e.symm_apply_apply, he.apply_symm_apply]
    exact Subtype.ext (comm y)
  · intro h
    exact Normal.of_equiv_equiv (f := e) (g := mapFieldEquiv e f comm S)
      (mapFieldEquiv_commutes e f comm S)

/-- Formation of the normal closure is preserved by an embedding of normal ambient extensions. -/
theorem mapField_normalClosure [Normal K M] [Normal K' M'] (S : IntermediateField K M) :
    mapField e f comm (IntermediateField.normalClosure K S M) =
      IntermediateField.normalClosure K' (mapField e f comm S) M' := by
  let T := IntermediateField.normalClosure K' (mapField e f comm S) M'
  let U : IntermediateField K M :=
    { T.toSubfield.comap f with
      algebraMap_mem' := fun x => by
        change f (algebraMap K M x) ∈ T
        rw [comm]
        exact T.algebraMap_mem _ }
  have : Normal K' (mapField e f comm (IntermediateField.normalClosure K S M)) :=
    (normal_mapField_iff e f comm _).mpr inferInstance
  have hT : T ≤ mapField e f comm (IntermediateField.normalClosure K S M) :=
    IntermediateField.normalClosure_le_iff_of_normal.mpr
      (mapField_mono e f comm (IntermediateField.le_normalClosure S))
  have hU : mapField e f comm U = T := by
    ext x
    change (∃ y : M, f y ∈ T ∧ f y = x) ↔ x ∈ T
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      obtain ⟨y, _, rfl⟩ :=
        (mem_mapField e f comm (IntermediateField.normalClosure K S M) x).mp (hT hx)
      exact ⟨y, hx, rfl⟩
  have : Normal K U := (normal_mapField_iff e f comm U).mp (by rw [hU]; infer_instance)
  have hle : S ≤ U := fun x hx =>
    IntermediateField.le_normalClosure (mapField e f comm S) ⟨x, hx, rfl⟩
  refine le_antisymm ?_ hT
  change _ ≤ T
  rw [← hU]
  exact mapField_mono e f comm (IntermediateField.normalClosure_le_iff_of_normal.mpr hle)

end ImageTransport
end MackeyCompletion
end Langlands.Global.Harris
