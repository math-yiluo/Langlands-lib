/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.AlgebraicGeometry.OpensGlueData
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-!
# Relative gluing data

Fix a scheme `T`, a finite family of `T`-schemes `pₐ : Yₐ ⟶ T` and a morphism `β : B ⟶ T`.
A relative gluing datum over `β` consists of opens `V a b` of the base changed charts
`Yₐ ×_T B` and morphisms `ψ a b : V a b ⟶ Y_b` over `T`; the associated overlap maps
`V a b ⟶ Y_b ×_T B` are morphisms over `B`. If the datum satisfies the gluing axioms
(`AlgebraicGeometry.RelativeGluingDatum.IsValid`), the charts `Yₐ ×_T B` glue to a scheme over `B`.

The point of this formulation is that all overlap maps take values in the fixed schemes `Y_b`,
so that the datum can be transported along any morphism `γ : B' ⟶ B` over `T`
(`AlgebraicGeometry.RelativeGluingDatum.transport`), e.g. between the stages of a cofiltered
system.

## Main definitions

- `AlgebraicGeometry.RelativeGluingDatum.IsOpenValid`,
  `AlgebraicGeometry.RelativeGluingDatum.IsValid`: the gluing axioms.
- `AlgebraicGeometry.RelativeGluingDatum.toOpensGlueData`,
  `AlgebraicGeometry.RelativeGluingDatum.glued`, `AlgebraicGeometry.RelativeGluingDatum.toBase`:
  the glued scheme over `B`.
- `AlgebraicGeometry.RelativeGluingDatum.transport`,
  `AlgebraicGeometry.RelativeGluingDatum.IsTransport`: transport along `γ : B' ⟶ B`.
- `AlgebraicGeometry.RelativeGluingDatum.IsCompatible`: compatibility of a datum with a family of
  open immersions `ℓₐ : Yₐ ×_T B ⟶ X`; compatible data are valid.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {J : Type u} {T : Scheme.{u}} {Y : J → Scheme.{u}} (p : ∀ a, Y a ⟶ T)

/-- A relative gluing datum over `β : B ⟶ T` for the family `pₐ : Yₐ ⟶ T`: opens `V a b` of the
charts `Yₐ ×_T B` and morphisms `ψ a b : V a b ⟶ Y_b` over `T`. -/
structure RelativeGluingDatum {B : Scheme.{u}} (β : B ⟶ T) where
  /-- The overlap of the chart `a` with the chart `b`, as an open of the chart `a`. -/
  V (a b : J) : (pullback (p a) β).Opens
  /-- The first component of the overlap map `V a b ⟶ Y_b ×_T B`. -/
  ψ (a b : J) : (V a b).toScheme ⟶ Y b
  /-- The overlap maps lie over `T`. -/
  ψ_comp (a b : J) : ψ a b ≫ p b = (V a b).ι ≫ pullback.fst (p a) β ≫ p a

namespace RelativeGluingDatum

variable {p} {B : Scheme.{u}} {β : B ⟶ T} (d : RelativeGluingDatum p β)

/-- The overlap map `V a b ⟶ Y_b ×_T B`, a morphism over `B`. -/
noncomputable def map (a b : J) : (d.V a b).toScheme ⟶ pullback (p b) β :=
  pullback.lift (d.ψ a b) ((d.V a b).ι ≫ pullback.snd _ _) (by
    rw [d.ψ_comp, Category.assoc, pullback.condition])

@[reassoc (attr := simp)]
lemma map_fst (a b : J) : d.map a b ≫ pullback.fst _ _ = d.ψ a b := pullback.lift_fst ..

@[reassoc (attr := simp)]
lemma map_snd (a b : J) : d.map a b ≫ pullback.snd _ _ = (d.V a b).ι ≫ pullback.snd _ _ :=
  pullback.lift_snd ..

/-- The open part of the gluing axioms: `V a a` is everything, and the overlap map `a → b`
maps `V a b ⊓ V a c` into `V b c`. -/
structure IsOpenValid : Prop where
  V_self (a : J) : d.V a a = ⊤
  le_preimage (a b c : J) : (d.V a b).ι ⁻¹ᵁ d.V a c ≤ d.map a b ⁻¹ᵁ d.V b c

lemma IsOpenValid.range_map_subset {d : RelativeGluingDatum p β} (h : d.IsOpenValid) (a b : J) :
    Set.range (d.map a b) ⊆ (d.V b a : Set ↥(pullback (p b) β)) := by
  rintro _ ⟨x, rfl⟩
  refine h.le_preimage a b a ?_
  rw [h.V_self a]
  trivial

lemma IsOpenValid.range_homOfLE_map_subset {d : RelativeGluingDatum p β} (h : d.IsOpenValid)
    (a b c : J) :
    Set.range ((pullback (p a) β).homOfLE (inf_le_left : d.V a b ⊓ d.V a c ≤ d.V a b) ≫
      d.map a b) ⊆ (d.V b c : Set ↥(pullback (p b) β)) := by
  rintro _ ⟨x, rfl⟩
  rw [Scheme.Hom.comp_apply]
  refine h.le_preimage a b c ?_
  have e := Scheme.homOfLE_apply (X := pullback (p a) β)
    (inf_le_left : d.V a b ⊓ d.V a c ≤ d.V a b) x
  simp only [Scheme.Hom.mem_preimage, Scheme.Opens.ι_apply, e]
  exact x.2.2

/-- The overlap map `a → b` restricted to `V a b ⊓ V a c`, with values in `V b c`. -/
noncomputable def cocycleMap {d : RelativeGluingDatum p β} (h : d.IsOpenValid) (a b c : J) :
    (d.V a b ⊓ d.V a c).toScheme ⟶ (d.V b c).toScheme :=
  IsOpenImmersion.lift (d.V b c).ι
    ((pullback (p a) β).homOfLE inf_le_left ≫ d.map a b) (by
      rw [Scheme.Opens.range_ι]
      exact h.range_homOfLE_map_subset a b c)

@[reassoc (attr := simp)]
lemma cocycleMap_ι {d : RelativeGluingDatum p β} (h : d.IsOpenValid) (a b c : J) :
    cocycleMap h a b c ≫ (d.V b c).ι = (pullback (p a) β).homOfLE inf_le_left ≫ d.map a b :=
  IsOpenImmersion.lift_fac _ _ _

/-- The gluing axioms: the open part `AlgebraicGeometry.RelativeGluingDatum.IsOpenValid`, the
identity condition and the cocycle condition. -/
structure IsValid : Prop where
  isOpenValid : d.IsOpenValid
  ψ_self (a : J) : d.ψ a a = (d.V a a).ι ≫ pullback.fst _ _
  cocycle (a b c : J) : cocycleMap isOpenValid a b c ≫ d.ψ b c =
    (pullback (p a) β).homOfLE inf_le_right ≫ d.ψ a c

variable {d}

lemma IsValid.map_self (h : d.IsValid) (a : J) : d.map a a = (d.V a a).ι := by
  apply pullback.hom_ext
  · rw [map_fst, h.ψ_self]
  · rw [map_snd]

lemma IsValid.cocycleMap_map (h : d.IsValid) (a b c : J) :
    cocycleMap h.isOpenValid a b c ≫ d.map b c =
      (pullback (p a) β).homOfLE inf_le_right ≫ d.map a c := by
  apply pullback.hom_ext
  · rw [Category.assoc, map_fst, h.cocycle, Category.assoc, map_fst]
  · simp

/-- The overlap isomorphisms `V a b ⟶ V b a` of a valid datum. -/
noncomputable def t (h : d.IsOpenValid) (a b : J) : (d.V a b).toScheme ⟶ (d.V b a).toScheme :=
  IsOpenImmersion.lift (d.V b a).ι (d.map a b) (by
    rw [Scheme.Opens.range_ι]
    exact h.range_map_subset a b)

@[reassoc (attr := simp)]
lemma t_ι (h : d.IsOpenValid) (a b : J) : t h a b ≫ (d.V b a).ι = d.map a b :=
  IsOpenImmersion.lift_fac _ _ _

/-- The `AlgebraicGeometry.Scheme.OpensGlueData` of a valid relative gluing datum. -/
noncomputable def toOpensGlueData (h : d.IsValid) : Scheme.OpensGlueData.{u} where
  J := J
  U a := pullback (p a) β
  V := d.V
  V_self := h.isOpenValid.V_self
  t := t h.isOpenValid
  t_self a := by
    rw [← cancel_mono (d.V a a).ι, t_ι, h.map_self, Category.id_comp]
  t_mem a b c x hx := by
    have hx' : x ∈ (d.V a b).ι ⁻¹ᵁ d.V a c := hx
    have := h.isOpenValid.le_preimage a b c hx'
    rwa [Scheme.Hom.mem_preimage, ← t_ι h.isOpenValid, Scheme.Hom.comp_apply] at this
  cocycle a b c := by
    have e : IsOpenImmersion.lift (d.V b c).ι
        ((pullback (p a) β).homOfLE inf_le_left ≫ t h.isOpenValid a b ≫ (d.V b a).ι) (by
          rw [t_ι, Scheme.Opens.range_ι]
          exact h.isOpenValid.range_homOfLE_map_subset a b c) =
        cocycleMap h.isOpenValid a b c := by
      rw [← cancel_mono (d.V b c).ι, IsOpenImmersion.lift_fac, cocycleMap_ι, t_ι]
    rw [e, t_ι, t_ι, h.cocycleMap_map]

/-- The scheme over `B` obtained by gluing the charts `Yₐ ×_T B` of a valid relative gluing
datum along the opens `V a b` via the overlap maps. -/
noncomputable def glued (h : d.IsValid) : Scheme.{u} := (toOpensGlueData h).glued

/-- The open immersion of the chart `Yₐ ×_T B` into the glued scheme. -/
noncomputable def ι (h : d.IsValid) (a : J) : pullback (p a) β ⟶ glued h :=
  (toOpensGlueData h).ι a

instance (h : d.IsValid) (a : J) : IsOpenImmersion (ι h a) :=
  inferInstanceAs (IsOpenImmersion ((toOpensGlueData h).ι a))

@[reassoc]
lemma glue_condition (h : d.IsValid) (a b : J) :
    d.map a b ≫ ι h b = (d.V a b).ι ≫ ι h a := by
  rw [← t_ι h.isOpenValid, Category.assoc]
  exact (toOpensGlueData h).glue_condition a b

/-- The structure morphism of the glued scheme to `B`. -/
noncomputable def toBase (h : d.IsValid) : glued h ⟶ B :=
  (toOpensGlueData h).glueMorphisms (fun a ↦ pullback.snd (p a) β) (fun a b ↦ by
    simp only [toOpensGlueData]
    rw [t_ι_assoc, map_snd])

@[reassoc (attr := simp)]
lemma ι_toBase (h : d.IsValid) (a : J) : ι h a ≫ toBase h = pullback.snd (p a) β :=
  (toOpensGlueData h).ι_glueMorphisms _ _ a

lemma ι_hom_ext (h : d.IsValid) {Z : Scheme.{u}} {f₁ f₂ : glued h ⟶ Z}
    (e : ∀ a, ι h a ≫ f₁ = ι h a ≫ f₂) : f₁ = f₂ :=
  (toOpensGlueData h).hom_ext e

lemma iSup_opensRange_ι (h : d.IsValid) : ⨆ a, (ι h a).opensRange = ⊤ :=
  (toOpensGlueData h).iSup_opensRange_ι

lemma preimage_opensRange_ι (h : d.IsValid) (a b : J) :
    ι h a ⁻¹ᵁ (ι h b).opensRange = d.V a b :=
  (toOpensGlueData h).preimage_opensRange_ι a b

instance locallyOfFinitePresentation_toBase (h : d.IsValid)
    [∀ a, LocallyOfFinitePresentation (p a)] : LocallyOfFinitePresentation (toBase h) := by
  refine (Scheme.OpensGlueData.iff_forall_ι_comp (toOpensGlueData h)
    @LocallyOfFinitePresentation (toBase h)).mpr fun a ↦ ?_
  have e : (toOpensGlueData h).ι a ≫ toBase h = pullback.snd (p a) β := ι_toBase h a
  rw [e]
  exact MorphismProperty.pullback_snd _ _ inferInstance

instance compactSpace_glued (h : d.IsValid) [Finite J] [∀ a, CompactSpace ↥(pullback (p a) β)] :
    CompactSpace (glued h) := by
  have : Finite (toOpensGlueData h).J := ‹Finite J›
  have : ∀ a, CompactSpace ((toOpensGlueData h).U a) := ‹∀ a, CompactSpace _›
  exact Scheme.OpensGlueData.compactSpace_glued (toOpensGlueData h)

/-- A finite gluing of affine charts along quasi-compact overlaps is quasi-separated. -/
lemma quasiSeparatedSpace_glued (h : d.IsValid) [∀ a, IsAffine (pullback (p a) β)]
    (hV : ∀ a b, IsCompact (d.V a b : Set ↥(pullback (p a) β))) :
    QuasiSeparatedSpace (glued h) := by
  refine Scheme.quasiSeparatedSpace_of_isOpenCover (fun a ↦ (ι h a).opensRange)
    (iSup_opensRange_ι h) (fun a ↦ isAffineOpen_opensRange _) fun a b ↦ ?_
  have e := (toOpensGlueData h).opensRange_ι_inf_opensRange_ι a b
  have e' : ((ι h a).opensRange : Set (glued h)) ∩ (ι h b).opensRange =
      (ι h a) '' (d.V a b) := congrArg (fun U : (glued h).Opens ↦ (U : Set (glued h))) e
  rw [e']
  exact (hV a b).image (ι h a).continuous

/-! ### Transport along a morphism of bases -/

variable (p) {B' : Scheme.{u}} {β' : B' ⟶ T} (γ : B' ⟶ B) (w : γ ≫ β = β')

/-- The comparison map `Yₐ ×_T B' ⟶ Yₐ ×_T B` induced by `γ : B' ⟶ B` over `T`. -/
noncomputable def chartMap (a : J) : pullback (p a) β' ⟶ pullback (p a) β :=
  pullback.map _ _ _ _ (𝟙 _) γ (𝟙 _) (by simp) (by simp [w])

@[reassoc (attr := simp)]
lemma chartMap_fst (a : J) : chartMap p γ w a ≫ pullback.fst _ _ = pullback.fst _ _ := by
  simp [chartMap]

@[reassoc (attr := simp)]
lemma chartMap_snd (a : J) : chartMap p γ w a ≫ pullback.snd _ _ = pullback.snd _ _ ≫ γ := by
  simp [chartMap]

lemma chartMap_comp {B'' : Scheme.{u}} {β'' : B'' ⟶ T} (γ' : B'' ⟶ B') (w' : γ' ≫ β' = β'')
    (a : J) : chartMap p γ' w' a ≫ chartMap p γ w a =
      chartMap p (γ' ≫ γ) (by rw [Category.assoc, w, w']) a := by
  apply pullback.hom_ext <;> simp

variable {p}

/-- The transport of a relative gluing datum along `γ : B' ⟶ B`: the opens are pulled back and
the overlap maps are restricted. -/
noncomputable def transport (d : RelativeGluingDatum p β) : RelativeGluingDatum p β' where
  V a b := chartMap p γ w a ⁻¹ᵁ d.V a b
  ψ a b := (chartMap p γ w a).resLE (d.V a b) _ le_rfl ≫ d.ψ a b
  ψ_comp a b := by
    rw [Category.assoc, d.ψ_comp, Scheme.Hom.resLE_comp_ι_assoc, chartMap_fst_assoc]

/-- `d'` is the transport of `d` along `γ`, up to the choice of the proofs of the inclusions. -/
structure IsTransport (d' : RelativeGluingDatum p β') (d : RelativeGluingDatum p β) : Prop where
  V_eq (a b : J) : d'.V a b = chartMap p γ w a ⁻¹ᵁ d.V a b
  ψ_eq (a b : J) : d'.ψ a b = (chartMap p γ w a).resLE (d.V a b) (d'.V a b) (V_eq a b).le ≫
    d.ψ a b

lemma isTransport_transport (d : RelativeGluingDatum p β) :
    IsTransport γ w (d.transport γ w) d :=
  ⟨fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩

variable {γ w}

@[reassoc]
lemma IsTransport.map_chartMap {d' : RelativeGluingDatum p β'} {d : RelativeGluingDatum p β}
    (h : IsTransport γ w d' d) (a b : J) :
    d'.map a b ≫ chartMap p γ w b =
      (chartMap p γ w a).resLE (d.V a b) (d'.V a b) (h.V_eq a b).le ≫ d.map a b := by
  apply pullback.hom_ext
  · rw [Category.assoc, chartMap_fst, map_fst, Category.assoc, map_fst, h.ψ_eq]
  · simp

lemma IsTransport.trans {B'' : Scheme.{u}} {β'' : B'' ⟶ T} {γ' : B'' ⟶ B'}
    {w' : γ' ≫ β' = β''} {d'' : RelativeGluingDatum p β''} {d' : RelativeGluingDatum p β'}
    {d : RelativeGluingDatum p β} (h' : IsTransport γ' w' d'' d') (h : IsTransport γ w d' d) :
    IsTransport (γ' ≫ γ) (by rw [Category.assoc, w, w']) d'' d where
  V_eq a b := by rw [h'.V_eq, h.V_eq, ← Scheme.Hom.comp_preimage, chartMap_comp]
  ψ_eq a b := by
    rw [h'.ψ_eq, h.ψ_eq, ← Category.assoc, Scheme.Hom.resLE_comp_resLE]
    congr 1
    rw [← cancel_mono (d.V a b).ι, Scheme.Hom.resLE_comp_ι, Scheme.Hom.resLE_comp_ι,
      chartMap_comp]

lemma IsTransport.preimage_ι_eq {d' : RelativeGluingDatum p β'} {d : RelativeGluingDatum p β}
    (h : IsTransport γ w d' d) (a b c : J) :
    (d'.V a b).ι ⁻¹ᵁ d'.V a c = (chartMap p γ w a).resLE (d.V a b) (d'.V a b)
      (h.V_eq a b).le ⁻¹ᵁ ((d.V a b).ι ⁻¹ᵁ d.V a c) := by
  rw [← Scheme.Hom.comp_preimage, Scheme.Hom.resLE_comp_ι, Scheme.Hom.comp_preimage,
    h.V_eq a c]

lemma IsTransport.preimage_map_eq {d' : RelativeGluingDatum p β'} {d : RelativeGluingDatum p β}
    (h : IsTransport γ w d' d) (a b c : J) :
    d'.map a b ⁻¹ᵁ d'.V b c = (chartMap p γ w a).resLE (d.V a b) (d'.V a b)
      (h.V_eq a b).le ⁻¹ᵁ (d.map a b ⁻¹ᵁ d.V b c) := by
  rw [← Scheme.Hom.comp_preimage, ← h.map_chartMap, Scheme.Hom.comp_preimage, h.V_eq b c]

lemma IsTransport.isOpenValid {d' : RelativeGluingDatum p β'} {d : RelativeGluingDatum p β}
    (h : IsTransport γ w d' d) (hd : d.IsOpenValid) : d'.IsOpenValid where
  V_self a := by rw [h.V_eq, hd.V_self, Scheme.Hom.preimage_top]
  le_preimage a b c := by
    rw [h.preimage_ι_eq, h.preimage_map_eq]
    exact Scheme.Hom.preimage_mono _ (hd.le_preimage a b c)

lemma IsTransport.resLE_cocycleMap {d' : RelativeGluingDatum p β'}
    {d : RelativeGluingDatum p β} (h : IsTransport γ w d' d) (hd : d.IsOpenValid)
    (hd' : d'.IsOpenValid) (a b c : J) (W : (pullback (p a) β').Opens)
    (e : W ≤ chartMap p γ w a ⁻¹ᵁ (d.V a b ⊓ d.V a c)) (e' : W ≤ d'.V a b ⊓ d'.V a c) :
    (chartMap p γ w a).resLE _ W e ≫ cocycleMap hd a b c =
      (pullback (p a) β').homOfLE e' ≫ cocycleMap hd' a b c ≫
        (chartMap p γ w b).resLE (d.V b c) (d'.V b c) (h.V_eq b c).le := by
  have aux : (chartMap p γ w a).resLE _ W e ≫ (pullback (p a) β).homOfLE inf_le_left =
      (pullback (p a) β').homOfLE e' ≫ (pullback (p a) β').homOfLE inf_le_left ≫
        (chartMap p γ w a).resLE (d.V a b) (d'.V a b) (h.V_eq a b).le := by
    rw [← cancel_mono (d.V a b).ι]
    simp
  rw [← cancel_mono (d.V b c).ι]
  simp only [Category.assoc, cocycleMap_ι, Scheme.Hom.resLE_comp_ι, cocycleMap_ι_assoc,
    h.map_chartMap]
  rw [reassoc_of% aux]

lemma IsTransport.resLE_cocycle_left {d' : RelativeGluingDatum p β'}
    {d : RelativeGluingDatum p β} (h : IsTransport γ w d' d) (hd : d.IsOpenValid)
    (hd' : d'.IsOpenValid) (a b c : J) (W : (pullback (p a) β').Opens)
    (e : W ≤ chartMap p γ w a ⁻¹ᵁ (d.V a b ⊓ d.V a c)) (e' : W ≤ d'.V a b ⊓ d'.V a c) :
    (chartMap p γ w a).resLE _ W e ≫ cocycleMap hd a b c ≫ d.ψ b c =
      (pullback (p a) β').homOfLE e' ≫ cocycleMap hd' a b c ≫ d'.ψ b c := by
  rw [reassoc_of% h.resLE_cocycleMap hd hd' a b c W e e', h.ψ_eq b c]

lemma IsTransport.resLE_cocycle_right {d' : RelativeGluingDatum p β'}
    {d : RelativeGluingDatum p β} (h : IsTransport γ w d' d) (a b c : J)
    (W : (pullback (p a) β').Opens)
    (e : W ≤ chartMap p γ w a ⁻¹ᵁ (d.V a b ⊓ d.V a c)) (e' : W ≤ d'.V a b ⊓ d'.V a c) :
    (chartMap p γ w a).resLE _ W e ≫ (pullback (p a) β).homOfLE inf_le_right ≫ d.ψ a c =
      (pullback (p a) β').homOfLE e' ≫ (pullback (p a) β').homOfLE inf_le_right ≫
        d'.ψ a c := by
  have aux : (chartMap p γ w a).resLE _ W e ≫ (pullback (p a) β).homOfLE inf_le_right =
      (pullback (p a) β').homOfLE e' ≫ (pullback (p a) β').homOfLE inf_le_right ≫
        (chartMap p γ w a).resLE (d.V a c) (d'.V a c) (h.V_eq a c).le := by
    rw [← cancel_mono (d.V a c).ι]
    simp
  rw [reassoc_of% aux, h.ψ_eq a c]


/-! ### Data compatible with a family of open immersions -/

variable {X : Scheme.{u}} (ℓ : ∀ a, pullback (p a) β ⟶ X) [∀ a, IsOpenImmersion (ℓ a)]

/-- A relative gluing datum is compatible with the family `ℓₐ : Yₐ ×_T B ⟶ X` if `V a b` is the
locus of the chart `a` mapping into the image of the chart `b`, and the overlap maps commute
with the `ℓ`. -/
structure IsCompatible (d : RelativeGluingDatum p β) : Prop where
  V_eq (a b : J) : d.V a b = ℓ a ⁻¹ᵁ (ℓ b).opensRange
  map_comp (a b : J) : d.map a b ≫ ℓ b = (d.V a b).ι ≫ ℓ a

variable {ℓ}

/-- A datum compatible with a family of open immersions satisfies the gluing axioms. -/
lemma IsCompatible.isValid (h : IsCompatible ℓ d) : d.IsValid := by
  have hov : d.IsOpenValid := by
    refine ⟨fun a ↦ ?_, fun a b c ↦ ?_⟩
    · rw [h.V_eq, ← top_le_iff]
      rintro x -
      exact ⟨x, rfl⟩
    · rw [h.V_eq a c, h.V_eq b c, ← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage,
        h.map_comp]
  refine ⟨hov, fun a ↦ ?_, fun a b c ↦ ?_⟩
  · have : d.map a a = (d.V a a).ι := by
      rw [← cancel_mono (ℓ a), h.map_comp]
    rw [← this, map_fst]
  · have : cocycleMap hov a b c ≫ d.map b c =
        (pullback (p a) β).homOfLE inf_le_right ≫ d.map a c := by
      rw [← cancel_mono (ℓ c), Category.assoc, h.map_comp, cocycleMap_ι_assoc, Category.assoc,
        h.map_comp, Scheme.homOfLE_ι_assoc, h.map_comp, Scheme.homOfLE_ι_assoc]
    rw [← map_fst, ← Category.assoc, this, Category.assoc, map_fst]

/-- Compatibility only depends on the transported datum up to the choice of proofs. -/
lemma IsCompatible.of_isTransport {d₁ d₂ : RelativeGluingDatum p β}
    {d₀ : RelativeGluingDatum p β'} {γ₁ γ₂ : B ⟶ B'} {w₁ : γ₁ ≫ β' = β} {w₂ : γ₂ ≫ β' = β}
    (h₁ : IsTransport γ₁ w₁ d₁ d₀) (h₂ : IsTransport γ₂ w₂ d₂ d₀) (hγ : γ₁ = γ₂)
    (hc : IsCompatible ℓ d₁) : IsCompatible ℓ d₂ := by
  subst hγ
  have hV (a b : J) : d₂.V a b = d₁.V a b := by rw [h₁.V_eq, h₂.V_eq]
  refine ⟨fun a b ↦ by rw [hV, hc.V_eq], fun a b ↦ ?_⟩
  have : d₂.map a b = (pullback (p a) β).homOfLE (hV a b).le ≫ d₁.map a b := by
    apply pullback.hom_ext
    · rw [map_fst, Category.assoc, map_fst, h₂.ψ_eq, h₁.ψ_eq, ← Category.assoc]
      congr 1
      rw [← cancel_mono (d₀.V a b).ι, Scheme.Hom.resLE_comp_ι, Category.assoc,
        Scheme.Hom.resLE_comp_ι, Scheme.homOfLE_ι_assoc]
    · rw [map_snd, Category.assoc, map_snd, Scheme.homOfLE_ι_assoc]
  rw [this, Category.assoc, hc.map_comp, Scheme.homOfLE_ι_assoc]

end RelativeGluingDatum

end AlgebraicGeometry
