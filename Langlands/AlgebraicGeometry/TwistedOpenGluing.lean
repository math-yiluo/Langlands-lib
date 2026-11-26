import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_exists_quotient_of_forall_exists_quotient_restrict

/-! # Gluing open subschemes along transition maps that fix every point -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.TwistedOpenGluing

open P2MW.S_AlgebraicGeometry_Scheme_exists_quotient_of_forall_exists_quotient_restrict.AlgebraicGeometry.Scheme.GlueData
  (MkCore)

variable {C : Scheme.{u}}

/-- A morphism from an open subscheme to the ambient scheme that agrees with the inclusion on
underlying points. -/
def IsPointwiseInclusion {U : C.Opens} (f : U.toScheme ⟶ C) : Prop :=
  ∀ x : U.toScheme, f x = U.ι x

theorem IsPointwiseInclusion.homOfLE_comp {U W : C.Opens} {f : U.toScheme ⟶ C}
    (hf : IsPointwiseInclusion f) (h : W ≤ U) (x : W.toScheme) :
    (C.homOfLE h ≫ f) x = W.ι x := by
  rw [Scheme.Hom.comp_apply, hf, ← Scheme.Hom.comp_apply, Scheme.homOfLE_ι]

theorem IsPointwiseInclusion.range_subset {U W Q : C.Opens} {f : U.toScheme ⟶ C}
    (hf : IsPointwiseInclusion f) (hWU : W ≤ U) (hWQ : W ≤ Q) :
    Set.range (C.homOfLE hWU ≫ f) ⊆ Set.range Q.ι := by
  rintro _ ⟨x, rfl⟩
  rw [hf.homOfLE_comp, Scheme.Opens.range_ι]
  exact hWQ x.2

/-- Restriction of a pointwise inclusion to a smaller open, as a morphism into another open
that contains the smaller one. -/
def restrictTo {U : C.Opens} (f : U.toScheme ⟶ C) (hf : IsPointwiseInclusion f)
    {W Q : C.Opens} (hWU : W ≤ U) (hWQ : W ≤ Q) : W.toScheme ⟶ Q.toScheme :=
  IsOpenImmersion.lift Q.ι (C.homOfLE hWU ≫ f) (hf.range_subset hWU hWQ)

@[reassoc (attr := simp)]
theorem restrictTo_ι {U : C.Opens} (f : U.toScheme ⟶ C) (hf : IsPointwiseInclusion f)
    {W Q : C.Opens} (hWU : W ≤ U) (hWQ : W ≤ Q) :
    restrictTo f hf hWU hWQ ≫ Q.ι = C.homOfLE hWU ≫ f :=
  IsOpenImmersion.lift_fac _ _ _

/-- Gluing data: open subschemes `V i` of `C` and, for every pair, a transition `θ i j` from the
coordinates of the `j`-th piece on the overlap to those of the `i`-th piece. The transitions fix
every point of `C`, are the inclusions on the diagonal and satisfy the cocycle identity. -/
structure Data (C : Scheme.{u}) where
  /-- The index type. -/
  J : Type u
  /-- The pieces. -/
  V : J → C.Opens
  /-- The transition maps. -/
  θ : ∀ i j, (V i ⊓ V j).toScheme ⟶ C
  pointwise : ∀ i j, IsPointwiseInclusion (θ i j)
  self : ∀ i, θ i i = (V i ⊓ V i).ι
  cocycle : ∀ i j k,
    restrictTo (θ j k) (pointwise j k) (W := V i ⊓ V j ⊓ V k)
        (le_inf (inf_le_left.trans inf_le_right) inf_le_right) inf_le_left ≫ θ i j =
      C.homOfLE (le_inf (inf_le_left.trans inf_le_left) inf_le_right : V i ⊓ V j ⊓ V k ≤ V i ⊓ V k) ≫
        θ i k

namespace Data

variable (D : Data C)

/-- The overlap of the `i`-th and `j`-th pieces, as an open of the `i`-th piece. -/
abbrev O (i j : D.J) : (D.V i).toScheme.Opens := (D.V i).ι ⁻¹ᵁ D.V j

/-- The inclusion of a nested overlap into `C`. -/
abbrev nest (i j : D.J) : (D.O i j).toScheme ⟶ C := (D.O i j).ι ≫ (D.V i).ι

theorem range_nest (i j : D.J) : Set.range (D.nest i j) = ((D.V i ⊓ D.V j : C.Opens) : Set C) := by
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hi, hj⟩
    exact ⟨⟨x, hi⟩, hj, rfl⟩

/-- The nested overlap mapped onto the intersection. -/
def toInf (i j : D.J) : (D.O i j).toScheme ⟶ (D.V i ⊓ D.V j).toScheme :=
  IsOpenImmersion.lift (D.V i ⊓ D.V j).ι (D.nest i j) (by
    rw [range_nest, Scheme.Opens.range_ι])

@[reassoc (attr := simp)]
theorem toInf_ι (i j : D.J) : D.toInf i j ≫ (D.V i ⊓ D.V j).ι = D.nest i j :=
  IsOpenImmersion.lift_fac _ _ _

/-- The transition from the `i`-th piece to the `j`-th piece on their overlap. -/
def t (i j : D.J) : (D.O i j).toScheme ⟶ (D.O j i).toScheme :=
  IsOpenImmersion.lift (D.nest j i) (D.toInf i j ≫ C.homOfLE (inf_comm (D.V i) (D.V j)).le ≫ D.θ j i) (by
    rintro _ ⟨x, rfl⟩
    rw [range_nest, Scheme.Hom.comp_apply, (D.pointwise j i).homOfLE_comp]
    exact (inf_comm (D.V i) (D.V j)).le (D.toInf i j x).2)

@[reassoc (attr := simp)]
theorem t_nest (i j : D.J) :
    D.t i j ≫ D.nest j i = D.toInf i j ≫ C.homOfLE (inf_comm (D.V i) (D.V j)).le ≫ D.θ j i :=
  IsOpenImmersion.lift_fac _ _ _

theorem t_nest_apply (i j : D.J) (x : (D.O i j).toScheme) :
    D.nest j i (D.t i j x) = D.nest i j x := by
  rw [← Scheme.Hom.comp_apply, t_nest, Scheme.Hom.comp_apply, (D.pointwise j i).homOfLE_comp,
    ← Scheme.Hom.comp_apply, toInf_ι]

theorem t_self (i : D.J) : D.t i i = 𝟙 _ := by
  rw [← cancel_mono (D.nest i i), t_nest, D.self, Scheme.homOfLE_ι, toInf_ι, Category.id_comp]

theorem t_inter (i j k : D.J) :
    (D.O i j).ι ⁻¹ᵁ (D.O i k) ≤ D.t i j ⁻¹ᵁ ((D.O j i).ι ⁻¹ᵁ (D.O j k)) := by
  intro x hx
  change D.nest j i (D.t i j x) ∈ D.V k
  rw [t_nest_apply]
  exact hx

@[reassoc]
theorem restrictRestrictComm_hom_ι_ι (X : Scheme.{u}) (U V : X.Opens) :
    (X.restrictRestrictComm U V).hom ≫ (V.ι ⁻¹ᵁ U).ι ≫ V.ι = (U.ι ⁻¹ᵁ V).ι ≫ U.ι :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- The triple overlap inside the `i`-th piece mapped into the corresponding open of `C`. -/
def toTriple (i j k : D.J) :
    ((D.O i j).ι ⁻¹ᵁ (D.O i k)).toScheme ⟶ (D.V k ⊓ D.V j ⊓ D.V i).toScheme :=
  IsOpenImmersion.lift (D.V k ⊓ D.V j ⊓ D.V i).ι (((D.O i j).ι ⁻¹ᵁ (D.O i k)).ι ≫ D.nest i j) (by
    rintro _ ⟨x, rfl⟩
    have hk := (Scheme.Hom.mem_preimage _).mp ((Scheme.Hom.mem_preimage _).mp x.2)
    have hj := (Scheme.Hom.mem_preimage _).mp x.1.2
    have hi := x.1.1.2
    rw [Scheme.Opens.range_ι, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
    exact ⟨⟨hk, hj⟩, hi⟩)

@[reassoc (attr := simp)]
theorem toTriple_ι (i j k : D.J) :
    D.toTriple i j k ≫ (D.V k ⊓ D.V j ⊓ D.V i).ι = ((D.O i j).ι ⁻¹ᵁ (D.O i k)).ι ≫ D.nest i j :=
  IsOpenImmersion.lift_fac _ _ _

theorem cocycle_core (i j k : D.J) :
    ((D.t i j).resLE ((D.O j i).ι ⁻¹ᵁ (D.O j k)) ((D.O i j).ι ⁻¹ᵁ (D.O i k)) (D.t_inter i j k) ≫
      ((D.V j).toScheme.restrictRestrictComm (D.O j i) (D.O j k)).hom ≫
        ((D.O j k).ι ⁻¹ᵁ (D.O j i)).ι ≫ D.t j k ≫ (D.O k j).ι) =
    ((D.V i).toScheme.restrictRestrictComm (D.O i j) (D.O i k)).hom ≫
      ((D.O i k).ι ⁻¹ᵁ (D.O i j)).ι ≫ D.t i k ≫ (D.O k i).ι := by
  rw [← cancel_mono (D.V k).ι]
  simp only [Category.assoc]
  have hR : ((D.V i).toScheme.restrictRestrictComm (D.O i j) (D.O i k)).hom ≫
      ((D.O i k).ι ⁻¹ᵁ (D.O i j)).ι ≫ D.toInf i k ≫ C.homOfLE (inf_comm (D.V i) (D.V k)).le =
      D.toTriple i j k ≫ C.homOfLE (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
        D.V k ⊓ D.V j ⊓ D.V i ≤ D.V k ⊓ D.V i) := by
    rw [← cancel_mono (D.V k ⊓ D.V i).ι]
    simp only [Category.assoc, Scheme.homOfLE_ι, toInf_ι, toTriple_ι]
    exact restrictRestrictComm_hom_ι_ι_assoc _ _ _ _
  have hL : (D.t i j).resLE ((D.O j i).ι ⁻¹ᵁ (D.O j k)) ((D.O i j).ι ⁻¹ᵁ (D.O i k))
        (D.t_inter i j k) ≫
      ((D.V j).toScheme.restrictRestrictComm (D.O j i) (D.O j k)).hom ≫
        ((D.O j k).ι ⁻¹ᵁ (D.O j i)).ι ≫ D.toInf j k ≫ C.homOfLE (inf_comm (D.V j) (D.V k)).le =
      D.toTriple i j k ≫ restrictTo (D.θ j i) (D.pointwise j i) (W := D.V k ⊓ D.V j ⊓ D.V i)
        (le_inf (inf_le_left.trans inf_le_right) inf_le_right) inf_le_left := by
    rw [← cancel_mono (D.V k ⊓ D.V j).ι]
    simp only [Category.assoc, Scheme.homOfLE_ι, toInf_ι, restrictTo_ι]
    rw [restrictRestrictComm_hom_ι_ι_assoc, Scheme.Hom.resLE_comp_ι_assoc, t_nest]
    have h3 : ((D.O i j).ι ⁻¹ᵁ (D.O i k)).ι ≫ D.toInf i j ≫ C.homOfLE (inf_comm (D.V i) (D.V j)).le =
        D.toTriple i j k ≫ C.homOfLE (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
          D.V k ⊓ D.V j ⊓ D.V i ≤ D.V j ⊓ D.V i) := by
      rw [← cancel_mono (D.V j ⊓ D.V i).ι]
      simp only [Category.assoc, Scheme.homOfLE_ι, toInf_ι, toTriple_ι]
    rw [reassoc_of% h3]
  have hc := D.cocycle k j i
  calc _ = (D.t i j).resLE ((D.O j i).ι ⁻¹ᵁ (D.O j k)) ((D.O i j).ι ⁻¹ᵁ (D.O i k))
        (D.t_inter i j k) ≫
      ((D.V j).toScheme.restrictRestrictComm (D.O j i) (D.O j k)).hom ≫
        ((D.O j k).ι ⁻¹ᵁ (D.O j i)).ι ≫ D.toInf j k ≫ C.homOfLE (inf_comm (D.V j) (D.V k)).le ≫
          D.θ k j := by
        rw [← t_nest]
    _ = D.toTriple i j k ≫ C.homOfLE (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
          D.V k ⊓ D.V j ⊓ D.V i ≤ D.V k ⊓ D.V i) ≫ D.θ k i := by
        rw [reassoc_of% hL, hc]
    _ = _ := by
        rw [← reassoc_of% hR, t_nest]

/-- The gluing core of the data. -/
def core : MkCore.{u} where
  J := D.J
  U i := (D.V i).toScheme
  V i j := D.O i j
  t := D.t
  V_id _ := Scheme.Opens.ι_preimage_self _
  t_id := D.t_self
  t_inter := D.t_inter
  cocycle := D.cocycle_core

/-- The glued scheme. -/
abbrev glued : Scheme.{u} := D.core.glueData.glued

/-- The open immersion of a piece into the glued scheme. -/
abbrev ι (i : D.J) : (D.V i).toScheme ⟶ D.glued := D.core.glueData.ι i

instance (i : D.J) : IsOpenImmersion (D.ι i) :=
  Scheme.GlueData.ι_isOpenImmersion D.core.glueData i

/-- A point of the overlap in the `j`-th piece is glued to its image under `θ i j` in the
`i`-th piece. -/
theorem glue (i j : D.J) :
    C.homOfLE (inf_le_right : D.V i ⊓ D.V j ≤ D.V j) ≫ D.ι j =
      restrictTo (D.θ i j) (D.pointwise i j) le_rfl inf_le_left ≫ D.ι i := by
  have hg := MkCore.t_ι_ι D.core j i
  let b : (D.V i ⊓ D.V j).toScheme ⟶ (D.O j i).toScheme :=
    IsOpenImmersion.lift (D.nest j i) (D.V i ⊓ D.V j).ι (by
      rw [range_nest, Scheme.Opens.range_ι, inf_comm])
  have hb : b ≫ D.nest j i = (D.V i ⊓ D.V j).ι := IsOpenImmersion.lift_fac _ _ _
  have h1 : b ≫ (D.O j i).ι = C.homOfLE (inf_le_right : D.V i ⊓ D.V j ≤ D.V j) := by
    rw [← cancel_mono (D.V j).ι, Category.assoc, hb, Scheme.homOfLE_ι]
  have h2 : b ≫ D.t j i ≫ (D.O i j).ι = restrictTo (D.θ i j) (D.pointwise i j) le_rfl inf_le_left := by
    rw [← cancel_mono (D.V i).ι, Category.assoc, Category.assoc, restrictTo_ι, Scheme.homOfLE_rfl,
      Category.id_comp, t_nest]
    have h4 : b ≫ D.toInf j i ≫ C.homOfLE (inf_comm (D.V j) (D.V i)).le = 𝟙 _ := by
      rw [← cancel_mono (D.V i ⊓ D.V j).ι]
      simp only [Category.assoc, Scheme.homOfLE_ι, toInf_ι, hb, Category.id_comp]
    rw [reassoc_of% h4]
  rw [← h1, ← h2, Category.assoc, Category.assoc]
  exact congrArg (b ≫ ·) hg.symm

/-- A compatible family of morphisms on the pieces is compatible on the nested overlaps. -/
theorem core_compat {Y : Scheme.{u}} (m : ∀ i, (D.V i).toScheme ⟶ Y)
    (hm : ∀ i j, C.homOfLE (inf_le_right : D.V i ⊓ D.V j ≤ D.V j) ≫ m j =
      restrictTo (D.θ i j) (D.pointwise i j) le_rfl inf_le_left ≫ m i) (i j : D.J) :
    (D.O i j).ι ≫ m i = D.t i j ≫ (D.O j i).ι ≫ m j := by
  let d : (D.O i j).toScheme ⟶ (D.V j ⊓ D.V i).toScheme :=
    D.toInf i j ≫ C.homOfLE (inf_comm (D.V i) (D.V j)).le
  have hd₁ : d ≫ C.homOfLE (inf_le_right : D.V j ⊓ D.V i ≤ D.V i) = (D.O i j).ι := by
    rw [← cancel_mono (D.V i).ι]
    simp only [d, Category.assoc, Scheme.homOfLE_ι, toInf_ι]
  have hd₂ : d ≫ restrictTo (D.θ j i) (D.pointwise j i) le_rfl inf_le_left =
      D.t i j ≫ (D.O j i).ι := by
    rw [← cancel_mono (D.V j).ι]
    simp only [d, Category.assoc, restrictTo_ι, Scheme.homOfLE_rfl, Category.id_comp, t_nest]
  rw [← hd₁, Category.assoc, hm j i, ← Category.assoc, hd₂, Category.assoc]

/-- Morphisms out of the glued scheme from compatible morphisms on the pieces. -/
def desc {Y : Scheme.{u}} (m : ∀ i, (D.V i).toScheme ⟶ Y)
    (hm : ∀ i j, C.homOfLE (inf_le_right : D.V i ⊓ D.V j ≤ D.V j) ≫ m j =
      restrictTo (D.θ i j) (D.pointwise i j) le_rfl inf_le_left ≫ m i) :
    D.glued ⟶ Y :=
  Multicoequalizer.desc D.core.glueData.diagram _ m (by
    rintro ⟨i, j⟩
    exact D.core_compat m hm i j)

@[reassoc (attr := simp)]
theorem ι_desc {Y : Scheme.{u}} (m : ∀ i, (D.V i).toScheme ⟶ Y)
    (hm : ∀ i j, C.homOfLE (inf_le_right : D.V i ⊓ D.V j ≤ D.V j) ≫ m j =
      restrictTo (D.θ i j) (D.pointwise i j) le_rfl inf_le_left ≫ m i) (i : D.J) :
    D.ι i ≫ D.desc m hm = m i :=
  Multicoequalizer.π_desc _ _ _ _ _

theorem hom_ext {Y : Scheme.{u}} {f g : D.glued ⟶ Y} (h : ∀ i, D.ι i ≫ f = D.ι i ≫ g) :
    f = g :=
  Multicoequalizer.hom_ext _ _ _ h

theorem iSup_opensRange : ⨆ i, (D.ι i).opensRange = ⊤ :=
  D.core.glueData.openCover.iSup_opensRange

theorem preimage_opensRange (i j : D.J) : (D.ι i) ⁻¹ᵁ (D.ι j).opensRange = D.O i j :=
  MkCore.preimage_opensRange D.core i j

section Recognize

variable {Y : Scheme.{u}} (κ : ∀ i, (D.V i).toScheme ⟶ Y) [∀ i, IsOpenImmersion (κ i)]
  (hcov : ⨆ i, (κ i).opensRange = ⊤)
  (hpre : ∀ i j, (κ j) ⁻¹ᵁ (κ i).opensRange ≤ (D.V j).ι ⁻¹ᵁ D.V i)
  (hκ : ∀ i j, C.homOfLE (inf_le_right : D.V i ⊓ D.V j ≤ D.V j) ≫ κ j =
    restrictTo (D.θ i j) (D.pointwise i j) le_rfl inf_le_left ≫ κ i)

include hpre in
/-- The overlap of the images of two pieces, mapped back into the overlap of the pieces. -/
def overlapLift (i j : D.J) :
    ((κ i).opensRange ⊓ (κ j).opensRange).toScheme ⟶ (D.V i ⊓ D.V j).toScheme :=
  IsOpenImmersion.lift (D.V i ⊓ D.V j).ι
    (Y.homOfLE inf_le_right ≫ (κ j).isoOpensRange.inv ≫ (D.V j).ι) (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      let z := ((Y.homOfLE (inf_le_right : (κ i).opensRange ⊓ (κ j).opensRange ≤ _)) ≫
        (κ j).isoOpensRange.inv) y
      have hz : z ∈ (κ j) ⁻¹ᵁ (κ i).opensRange := by
        rw [Scheme.Hom.mem_preimage]
        change ((Y.homOfLE inf_le_right ≫ (κ j).isoOpensRange.inv) ≫ κ j) y ∈ _
        rw [Category.assoc, Scheme.Hom.isoOpensRange_inv_comp, Scheme.homOfLE_ι]
        exact y.2.1
      exact ⟨hpre i j hz, z.2⟩)

theorem overlapLift_homOfLE (i j : D.J) :
    D.overlapLift κ hpre i j ≫ C.homOfLE (inf_le_right : D.V i ⊓ D.V j ≤ D.V j) =
      Y.homOfLE inf_le_right ≫ (κ j).isoOpensRange.inv := by
  rw [← cancel_mono (D.V j).ι, Category.assoc, Scheme.homOfLE_ι, Category.assoc]
  exact IsOpenImmersion.lift_fac _ _ _

include hκ in
theorem overlapLift_restrictTo (i j : D.J) :
    D.overlapLift κ hpre i j ≫ restrictTo (D.θ i j) (D.pointwise i j) le_rfl inf_le_left =
      Y.homOfLE inf_le_left ≫ (κ i).isoOpensRange.inv := by
  rw [← cancel_mono (κ i), Category.assoc, ← hκ, Category.assoc,
    Scheme.Hom.isoOpensRange_inv_comp, reassoc_of% (D.overlapLift_homOfLE κ hpre i j),
    Scheme.Hom.isoOpensRange_inv_comp, Scheme.homOfLE_ι, Scheme.homOfLE_ι]

include hpre hκ in
/-- The inverse of the comparison morphism, glued on the cover by the images of the pieces. -/
def recognizeInv : Y ⟶ D.glued :=
  (Y.openCoverOfIsOpenCover (fun i ↦ (κ i).opensRange) hcov).glueMorphisms
    (fun (i : D.J) ↦ (κ i).isoOpensRange.inv ≫ D.ι i) (by
      intro (i : D.J) (j : D.J)
      let P := isPullback_opens_inf (κ i).opensRange (κ j).opensRange
      change pullback.fst (κ i).opensRange.ι (κ j).opensRange.ι ≫ (κ i).isoOpensRange.inv ≫ D.ι i =
        pullback.snd (κ i).opensRange.ι (κ j).opensRange.ι ≫ (κ j).isoOpensRange.inv ≫ D.ι j
      rw [← cancel_epi P.isoPullback.hom, P.isoPullback_hom_fst_assoc,
        P.isoPullback_hom_snd_assoc, ← reassoc_of% (D.overlapLift_restrictTo κ hpre hκ i j),
        ← reassoc_of% (D.overlapLift_homOfLE κ hpre i j), D.glue])

@[reassoc]
theorem ι_recognizeInv (i : D.J) :
    (κ i).opensRange.ι ≫ D.recognizeInv κ hcov hpre hκ = (κ i).isoOpensRange.inv ≫ D.ι i :=
  (Y.openCoverOfIsOpenCover (fun i ↦ (κ i).opensRange) hcov).ι_glueMorphisms
    (fun (i : D.J) ↦ (κ i).isoOpensRange.inv ≫ D.ι i) _ i

/-- A scheme covered by open immersions of the pieces, compatible with the transition maps, is
isomorphic to the glued scheme. -/
def recognize : D.glued ≅ Y where
  hom := D.desc κ hκ
  inv := D.recognizeInv κ hcov hpre hκ
  hom_inv_id := by
    refine D.hom_ext fun i ↦ ?_
    rw [ι_desc_assoc, Category.comp_id, ← Scheme.Hom.isoOpensRange_hom_ι (κ i), Category.assoc,
      ι_recognizeInv, Iso.hom_inv_id_assoc]
  inv_hom_id := by
    refine (Y.openCoverOfIsOpenCover (fun i ↦ (κ i).opensRange) hcov).hom_ext _ _
      fun (i : D.J) ↦ ?_
    change (κ i).opensRange.ι ≫ D.recognizeInv κ hcov hpre hκ ≫ D.desc κ hκ =
      (κ i).opensRange.ι ≫ 𝟙 Y
    rw [ι_recognizeInv_assoc, ι_desc, Scheme.Hom.isoOpensRange_inv_comp, Category.comp_id]

@[reassoc (attr := simp)]
theorem ι_recognize_hom (i : D.J) : D.ι i ≫ (D.recognize κ hcov hpre hκ).hom = κ i :=
  D.ι_desc κ hκ i

end Recognize

end Data

end Langlands.AlgebraicGeometry.TwistedOpenGluing
