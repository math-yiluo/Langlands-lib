/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# The spectrum of an algebraic extension as a limit over finite subextensions

Let `ks / k` be an algebraic field extension. The finite subextensions `K` of `ks / k` form a
nonempty directed poset `AlgebraicGeometry.FiniteIntermediateField k ks`, and `ks` is the
filtered colimit of the `K` in `CommRingCat`. Since `Spec` turns colimits into limits, `Spec ks`
is the cofiltered limit of the affine schemes `Spec K`
(`AlgebraicGeometry.FiniteIntermediateField.isLimitSpecCone`).

We also show that `Spec ks` is the limit of the "diagonal" system
`K ↦ Spec ks ×_{Spec K} Spec ks` (`AlgebraicGeometry.FiniteIntermediateField.isLimitDiagCone`):
two morphisms `T ⟶ Spec ks` agreeing after composition to every `Spec K` are equal.

Both systems have affine stages and affine transition maps, so they can be used with the
limit lemmas of `WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable (k ks : Type u) [Field k] [Field ks] [Algebra k ks]

/-- The finite subextensions of a field extension `ks / k`, ordered by inclusion. -/
abbrev FiniteIntermediateField : Type u :=
  {K : IntermediateField k ks // FiniteDimensional k K}

namespace FiniteIntermediateField

instance : OrderBot (FiniteIntermediateField k ks) where
  bot := ⟨⊥, inferInstance⟩
  bot_le K := bot_le (a := K.1)

instance : Nonempty (FiniteIntermediateField k ks) := ⟨⊥⟩

instance : IsDirectedOrder (FiniteIntermediateField k ks) where
  directed K L := by
    have := K.2
    have := L.2
    exact ⟨⟨K.1 ⊔ L.1, inferInstance⟩, le_sup_left (b := L.1), le_sup_right (a := K.1)⟩

instance : IsCofiltered (FiniteIntermediateField k ks)ᵒᵖ := inferInstance

/-- The diagram in `CommRingCat` of the finite subextensions of `ks / k`. -/
@[simps]
def ringDiagram : FiniteIntermediateField k ks ⥤ CommRingCat.{u} where
  obj K := .of K.1
  map {K L} f := CommRingCat.ofHom (IntermediateField.inclusion (leOfHom f)).toRingHom

/-- The field `ks`, as a cocone over its finite subextensions. -/
@[simps]
def ringCocone : Cocone (ringDiagram k ks) where
  pt := .of ks
  ι := { app K := CommRingCat.ofHom (algebraMap K.1 ks) }

lemma directed_restrictScalars :
    Directed (· ≤ ·) fun K : FiniteIntermediateField k ks ↦
      K.1.toSubalgebra.restrictScalars ℤ :=
  Monotone.directed_le fun _ _ h _ hx ↦ (show _ ≤ _ from h) hx

variable {k ks} in
/-- The transition map `Spec K' ⟶ Spec K` for finite subextensions `K ≤ K'`. -/
noncomputable abbrev specMap {K K' : FiniteIntermediateField k ks} (h : K ≤ K') :
    Spec (.of K'.1) ⟶ Spec (.of K.1) :=
  Spec.map (CommRingCat.ofHom (IntermediateField.inclusion h).toRingHom)

/-- The cofiltered diagram `K ↦ Spec K` over the finite subextensions `K` of `ks / k`. -/
noncomputable def specDiagram : (FiniteIntermediateField k ks)ᵒᵖ ⥤ Scheme.{u} :=
  (ringDiagram k ks).op ⋙ Scheme.Spec

@[simp]
lemma specDiagram_obj (K : (FiniteIntermediateField k ks)ᵒᵖ) :
    (specDiagram k ks).obj K = Spec (.of K.unop.1) := rfl

@[simp]
lemma specDiagram_map {K K' : (FiniteIntermediateField k ks)ᵒᵖ} (f : K ⟶ K') :
    (specDiagram k ks).map f = specMap (leOfHom f.unop) := rfl

instance (K : (FiniteIntermediateField k ks)ᵒᵖ) : IsAffine ((specDiagram k ks).obj K) :=
  inferInstanceAs (IsAffine (Spec _))

instance (K : (FiniteIntermediateField k ks)ᵒᵖ) : CompactSpace ((specDiagram k ks).obj K) :=
  inferInstanceAs (CompactSpace (Spec _))

instance (K : (FiniteIntermediateField k ks)ᵒᵖ) :
    QuasiSeparatedSpace ((specDiagram k ks).obj K) :=
  inferInstanceAs (QuasiSeparatedSpace (Spec _))

instance {K K' : (FiniteIntermediateField k ks)ᵒᵖ} (f : K ⟶ K') :
    IsAffineHom ((specDiagram k ks).map f) :=
  inferInstanceAs (IsAffineHom (Spec.map _))

/-- The cone over `specDiagram k ks` with point `Spec ks`. -/
noncomputable def specCone : Cone (specDiagram k ks) where
  pt := Spec (.of ks)
  π := { app K := Spec.map (CommRingCat.ofHom (algebraMap K.unop.1 ks))
         naturality _ _ f := (Scheme.Spec.mapCone (ringCocone k ks).op).π.naturality f }

@[simp]
lemma specCone_pt : (specCone k ks).pt = Spec (.of ks) := rfl

@[simp]
lemma specCone_π_app (K : (FiniteIntermediateField k ks)ᵒᵖ) :
    (specCone k ks).π.app K = Spec.map (CommRingCat.ofHom (algebraMap K.unop.1 ks)) := rfl

@[reassoc (attr := simp)]
lemma specCone_π_app_specMap {K K' : FiniteIntermediateField k ks} (h : K ≤ K') :
    Spec.map (CommRingCat.ofHom (algebraMap K'.1 ks)) ≫ specMap h =
      Spec.map (CommRingCat.ofHom (algebraMap K.1 ks)) :=
  (specCone k ks).w (homOfLE h).op

/-! ### The diagonal system -/

variable {k ks} in
/-- The fibre product `Spec ks ×_{Spec K} Spec ks`. -/
noncomputable abbrev diagObj (K : FiniteIntermediateField k ks) : Scheme.{u} :=
  pullback (Spec.map (CommRingCat.ofHom (algebraMap K.1 ks)))
    (Spec.map (CommRingCat.ofHom (algebraMap K.1 ks)))

variable {k ks} in
/-- The transition map `Spec ks ×_{Spec K'} Spec ks ⟶ Spec ks ×_{Spec K} Spec ks` for
`K ≤ K'`. -/
noncomputable def diagMap {K K' : FiniteIntermediateField k ks} (h : K ≤ K') :
    diagObj K' ⟶ diagObj K :=
  pullback.map _ _ _ _ (𝟙 _) (𝟙 _) (specMap h) (by simp) (by simp)

@[reassoc (attr := simp)]
lemma diagMap_fst {K K' : FiniteIntermediateField k ks} (h : K ≤ K') :
    diagMap h ≫ pullback.fst _ _ = pullback.fst _ _ := by
  simp [diagMap]

@[reassoc (attr := simp)]
lemma diagMap_snd {K K' : FiniteIntermediateField k ks} (h : K ≤ K') :
    diagMap h ≫ pullback.snd _ _ = pullback.snd _ _ := by
  simp [diagMap]

/-- The cofiltered diagram `K ↦ Spec ks ×_{Spec K} Spec ks` over the finite subextensions `K`
of `ks / k`. -/
@[simps]
noncomputable def diagDiagram : (FiniteIntermediateField k ks)ᵒᵖ ⥤ Scheme.{u} where
  obj K := diagObj K.unop
  map f := diagMap (leOfHom f.unop)
  map_id K := pullback.hom_ext (by simp) (by simp)
  map_comp f g := pullback.hom_ext (by simp) (by simp)

instance (K : (FiniteIntermediateField k ks)ᵒᵖ) : IsAffine ((diagDiagram k ks).obj K) :=
  inferInstanceAs (IsAffine (pullback _ _))

instance (K : (FiniteIntermediateField k ks)ᵒᵖ) : CompactSpace ((diagDiagram k ks).obj K) :=
  inferInstance

instance (K : (FiniteIntermediateField k ks)ᵒᵖ) :
    QuasiSeparatedSpace ((diagDiagram k ks).obj K) :=
  inferInstance

instance {K K' : (FiniteIntermediateField k ks)ᵒᵖ} (f : K ⟶ K') :
    IsAffineHom ((diagDiagram k ks).map f) :=
  isAffineHom_of_isAffine _

/-- The diagonal cone over `diagDiagram k ks` with point `Spec ks`. -/
@[simps pt]
noncomputable def diagCone : Cone (diagDiagram k ks) where
  pt := Spec (.of ks)
  π := { app K := pullback.lift (𝟙 _) (𝟙 _) rfl
         naturality _ _ _ := pullback.hom_ext (by simp) (by simp) }

@[simp]
lemma diagCone_π_app (K : (FiniteIntermediateField k ks)ᵒᵖ) :
    (diagCone k ks).π.app K = pullback.lift (𝟙 _) (𝟙 _) rfl := rfl

@[reassoc (attr := simp)]
lemma diagCone_π_app_fst (K : (FiniteIntermediateField k ks)ᵒᵖ) :
    (diagCone k ks).π.app K ≫ pullback.fst _ _ = 𝟙 _ := by
  simp

@[reassoc (attr := simp)]
lemma diagCone_π_app_snd (K : (FiniteIntermediateField k ks)ᵒᵖ) :
    (diagCone k ks).π.app K ≫ pullback.snd _ _ = 𝟙 _ := by
  simp

lemma diagCone_fst_eq (s : Cone (diagDiagram k ks)) (K : (FiniteIntermediateField k ks)ᵒᵖ) :
    s.π.app K ≫ pullback.fst _ _ = s.π.app (.op ⊥) ≫ pullback.fst _ _ := by
  rw [← s.w (homOfLE (bot_le (a := K.unop))).op, Category.assoc, diagDiagram_map, diagMap_fst]

lemma diagCone_snd_eq (s : Cone (diagDiagram k ks)) (K : (FiniteIntermediateField k ks)ᵒᵖ) :
    s.π.app K ≫ pullback.snd _ _ = s.π.app (.op ⊥) ≫ pullback.snd _ _ := by
  rw [← s.w (homOfLE (bot_le (a := K.unop))).op, Category.assoc, diagDiagram_map, diagMap_snd]

/-! ### The limit properties -/

variable [Algebra.IsAlgebraic k ks]

/-- Every element of an algebraic extension lies in a finite subextension. -/
lemma exists_mem (x : ks) : ∃ K : FiniteIntermediateField k ks, x ∈ K.1 :=
  ⟨⟨IntermediateField.adjoin k {x},
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)⟩,
    IntermediateField.mem_adjoin_simple_self k x⟩

lemma iSup_restrictScalars_eq_top :
    ⨆ K : FiniteIntermediateField k ks, (K.1.toSubalgebra.restrictScalars ℤ) = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  obtain ⟨K, hK⟩ := exists_mem k ks x
  exact Algebra.mem_iSup_of_mem (S := fun K : FiniteIntermediateField k ks ↦
    K.1.toSubalgebra.restrictScalars ℤ) K hK

/-- (Implementation) The ring homomorphism out of `ks` induced by a cocone. -/
noncomputable def ringDesc (s : Cocone (ringDiagram k ks)) : ks →+* s.pt :=
  ((Subalgebra.iSupLift (fun K : FiniteIntermediateField k ks ↦
      K.1.toSubalgebra.restrictScalars ℤ)
      (directed_restrictScalars k ks)
      (fun K ↦ by exact (s.ι.app K).hom.toIntAlgHom)
      (fun K L h ↦ AlgHom.ext fun x ↦
        (ConcreteCategory.congr_hom (s.w (homOfLE (show K ≤ L from fun _ hy ↦ h hy))) x).symm)
      ⊤ (iSup_restrictScalars_eq_top k ks).ge).comp Subalgebra.topEquiv.symm.toAlgHom).toRingHom

lemma ringDesc_val (s : Cocone (ringDiagram k ks)) (K : FiniteIntermediateField k ks)
    (x : K.1) : ringDesc k ks s (algebraMap K.1 ks x) = (s.ι.app K).hom x := by
  have h : Subalgebra.topEquiv.symm.toAlgHom (algebraMap K.1 ks x)
      = Subalgebra.inclusion (le_top : K.1.toSubalgebra.restrictScalars ℤ ≤ ⊤) x :=
    Subtype.ext rfl
  simp only [ringDesc, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.comp_apply, h,
    Subalgebra.iSupLift_inclusion]
  rfl

/-- An algebraic extension `ks / k` is the filtered colimit in `CommRingCat` of its finite
subextensions. -/
noncomputable def isColimitRingCocone : IsColimit (ringCocone k ks) where
  desc s := CommRingCat.ofHom (ringDesc k ks s)
  fac s K := by
    ext x
    exact ringDesc_val k ks s K x
  uniq s m hm := by
    ext x
    obtain ⟨K, hK⟩ := exists_mem k ks x
    exact (ConcreteCategory.congr_hom (hm K) ⟨x, hK⟩).trans
      (ringDesc_val k ks s K ⟨x, hK⟩).symm

/-- **`Spec ks` is the cofiltered limit of the `Spec K`** for the finite subextensions `K` of an
algebraic extension `ks / k`. -/
noncomputable def isLimitSpecCone : IsLimit (specCone k ks) :=
  (isLimitOfPreserves Scheme.Spec (isColimitRingCocone k ks).op).ofIsoLimit
    (Cone.ext (Iso.refl _) fun _ ↦ by simp)

lemma diagCone_fst_eq_snd (s : Cone (diagDiagram k ks)) :
    s.π.app (.op ⊥) ≫ pullback.fst _ _ = s.π.app (.op ⊥) ≫ pullback.snd _ _ :=
  (isLimitSpecCone k ks).hom_ext fun K ↦ by
    rw [← diagCone_fst_eq k ks s K, ← diagCone_snd_eq k ks s K, Category.assoc, Category.assoc,
      specCone_π_app,
      pullback.condition]

/-- **`Spec ks` is the limit of the diagonal system** `K ↦ Spec ks ×_{Spec K} Spec ks` over the
finite subextensions `K` of an algebraic extension `ks / k`. -/
noncomputable def isLimitDiagCone : IsLimit (diagCone k ks) where
  lift s := s.π.app (.op ⊥) ≫ pullback.fst _ _
  fac s K := pullback.hom_ext (by simp [diagCone_fst_eq]) (by
    simpa [diagCone_snd_eq k ks s K] using diagCone_fst_eq_snd k ks s)
  uniq s m hm := by
    rw [← hm]
    simp

end FiniteIntermediateField

end AlgebraicGeometry
