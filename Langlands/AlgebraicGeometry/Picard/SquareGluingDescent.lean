import Langlands.AlgebraicGeometry.Picard.SquareGluingRestrictionComposition
import Langlands.AlgebraicGeometry.Picard.SquareGluingCubes

/-! # Descent calculus for actual Picard square gluing data -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.SquareGluingDescent

section Leg

variable {W X Y Z : Scheme.{u}}

/-- Pullback of actual line bundles. -/
abbrev P (f : X ⟶ Y) : PicardGroupoid Y ⥤ PicardGroupoid X := PicardGroupoid.pullback f

/-- The composition comparison, with its nested source. -/
def pcH (f : X ⟶ Y) (g : Y ⟶ Z) (L : PicardGroupoid Z) :
    (P f).obj ((P g).obj L) ⟶ (P (f ≫ g)).obj L :=
  (PicardGroupoid.pullbackComp f g).hom.app L

/-- The inverse composition comparison, with its nested target. -/
def pcI (f : X ⟶ Y) (g : Y ⟶ Z) (L : PicardGroupoid Z) :
    (P (f ≫ g)).obj L ⟶ (P f).obj ((P g).obj L) :=
  (PicardGroupoid.pullbackComp f g).inv.app L

@[reassoc (attr := simp)]
lemma pcI_pcH (f : X ⟶ Y) (g : Y ⟶ Z) (L : PicardGroupoid Z) :
    pcI f g L ≫ pcH f g L = 𝟙 _ :=
  (PicardGroupoid.pullbackComp f g).inv_hom_id_app L

@[reassoc (attr := simp)]
lemma pcH_pcI (f : X ⟶ Y) (g : Y ⟶ Z) (L : PicardGroupoid Z) :
    pcH f g L ≫ pcI f g L = 𝟙 _ :=
  (PicardGroupoid.pullbackComp f g).hom_inv_id_app L

/-- The square comparison, with nested source and target. -/
def sqH {X₀ X₁ X₂ : Scheme.{u}} (i₁ : X₀ ⟶ X₁) (i₂ : X₀ ⟶ X₂) (j₁ : X₁ ⟶ Y) (j₂ : X₂ ⟶ Y)
    (w : i₁ ≫ j₁ = i₂ ≫ j₂) (L : PicardGroupoid Y) :
    (P i₁).obj ((P j₁).obj L) ⟶ (P i₂).obj ((P j₂).obj L) :=
  (PicardGroupoid.squarePullbackIso i₁ i₂ j₁ j₂ w).hom.app L

@[reassoc]
lemma pcH_nat (f : X ⟶ Y) (g : Y ⟶ Z) {L L' : PicardGroupoid Z} (a : L ⟶ L') :
    (P f).map ((P g).map a) ≫ pcH f g L' = pcH f g L ≫ (P (f ≫ g)).map a :=
  (PicardGroupoid.pullbackComp f g).hom.naturality a

/-- Associativity of the composition comparisons, in clean form. -/
lemma pc_assoc (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) (L : PicardGroupoid Z) :
    (P f).map (pcH g h L) ≫ pcH f (g ≫ h) L =
      pcH f g ((P h).obj L) ≫ pcH (f ≫ g) h L ≫ eqToHom (by rw [Category.assoc]) := by
  have e := congrArg (fun η ↦ η.app L) (PicardGroupoid.pullback_associativity f g h)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, eqToHom_app, Category.id_comp] at e
  change pcI f (g ≫ h) L ≫ (P f).map (pcI g h L) ≫ pcH f g ((P h).obj L) ≫
    pcH (f ≫ g) h L = eqToHom (by rw [Category.assoc]) at e
  have e' : pcH f g ((P h).obj L) ≫ pcH (f ≫ g) h L =
      (P f).map (pcH g h L) ≫ pcH f (g ≫ h) L ≫ eqToHom (by rw [Category.assoc]) := by
    rw [← e, pcH_pcI_assoc, ← Functor.map_comp_assoc, pcH_pcI, CategoryTheory.Functor.map_id,
      Category.id_comp]
  rw [reassoc_of% e']
  simp

variable {Y₀ Y₁ T₀ T₁ S₀ S₁ : Scheme.{u}}
  (i : Y₀ ⟶ Y₁) (ι : T₀ ⟶ T₁) (κ : S₀ ⟶ S₁)
  (g₁ : T₁ ⟶ Y₁) (g₀ : T₀ ⟶ Y₀) (h₁ : S₁ ⟶ T₁) (h₀ : S₀ ⟶ T₀)
  (k : ι ≫ g₁ = g₀ ≫ i) (l : κ ≫ h₁ = h₀ ≫ ι)
  (m : κ ≫ (h₁ ≫ g₁) = (h₀ ≫ g₀) ≫ i)

/-- The pasting identity of `square_paste`, solved for the composite square. -/
lemma paste_leg (L : PicardGroupoid Y₁) :
    sqH κ (h₀ ≫ g₀) (h₁ ≫ g₁) i m L =
      (P κ).map (pcI h₁ g₁ L) ≫ sqH κ h₀ h₁ ι l ((P g₁).obj L) ≫
        (P h₀).map (sqH ι g₀ g₁ i k L) ≫ pcH h₀ g₀ ((P i).obj L) := by
  have h := SquareGluingRestrictionComposition.square_paste i ι κ g₁ g₀ h₁ h₀ k l m L
  change (P κ).map (pcH h₁ g₁ L) ≫ sqH κ (h₀ ≫ g₀) (h₁ ≫ g₁) i m L =
    sqH κ h₀ h₁ ι l ((P g₁).obj L) ≫ (P h₀).map (sqH ι g₀ g₁ i k L) ≫
      pcH h₀ g₀ ((P i).obj L) at h
  rw [← h, ← Functor.map_comp_assoc, pcI_pcH, CategoryTheory.Functor.map_id,
    Category.id_comp]

end Leg

namespace Sq

variable (S : Sq.{u})

/-- The actual gluing data of the square. -/
abbrev GD := PicardGroupoid.SquareGluingData S.i₁ S.i₂

/-- The actual comparison functor of the square. -/
abbrev C : PicardGroupoid S.X ⥤ S.GD :=
  PicardGroupoid.squareGluingComparison S.i₁ S.i₂ S.j₁ S.j₂ S.w

end Sq

namespace CubeMap

variable {S T T' T'' : Sq.{u}}

/-- Restriction of actual gluing data along the cube. -/
def R (c : CubeMap S T) : S.GD ⥤ T.GD :=
  SquareGluingRestriction.pullback S.i₁ S.i₂ T.i₁ T.i₂ c.g₁ c.g₂ c.g₀ c.k₁ c.k₂

/-- The published comparison of pullback and restriction along the cube. -/
def cI (c : CubeMap S T) :
    PicardGroupoid.pullback c.t ⋙ T.C ≅ S.C ⋙ c.R :=
  SquareGluingRestrictionComparison.comparisonIso S.i₁ S.i₂ S.j₁ S.j₂ S.w c.t T.j₁ T.j₂
    T.i₁ T.i₂ T.w c.g₁ c.g₂ c.g₀ c.h₁ c.h₂ c.k₁ c.k₂

/-- The published composition of successive restrictions. -/
def Comp (c : CubeMap S T) (c' : CubeMap T T') : c.R ⋙ c'.R ≅ (comp c' c).R :=
  SquareGluingRestrictionComposition.pullbackComp S.i₁ S.i₂ T.i₁ T.i₂ T'.i₁ T'.i₂
    c.g₁ c.g₂ c.g₀ c'.g₁ c'.g₂ c'.g₀ c.k₁ c.k₂ c'.k₁ c'.k₂
    (comp c' c).k₁ (comp c' c).k₂

@[simp]
lemma R_map_left (c : CubeMap S T) {D D' : S.GD} (φ : D ⟶ D') :
    (c.R.map φ).left = (PicardGroupoid.pullback c.g₁).map φ.left := rfl

@[simp]
lemma R_map_right (c : CubeMap S T) {D D' : S.GD} (φ : D ⟶ D') :
    (c.R.map φ).right = (PicardGroupoid.pullback c.g₂).map φ.right := rfl

@[simp]
lemma R_obj_left (c : CubeMap S T) (D : S.GD) :
    (c.R.obj D).left = (PicardGroupoid.pullback c.g₁).obj D.left := rfl

@[simp]
lemma R_obj_right (c : CubeMap S T) (D : S.GD) :
    (c.R.obj D).right = (PicardGroupoid.pullback c.g₂).obj D.right := rfl

@[simp]
lemma cI_hom_app_left (c : CubeMap S T) (L : PicardGroupoid S.X) :
    ((cI c).hom.app L).left =
      (PicardGroupoid.squarePullbackIso T.j₁ c.g₁ c.t S.j₁ c.h₁).hom.app L := rfl

@[simp]
lemma cI_hom_app_right (c : CubeMap S T) (L : PicardGroupoid S.X) :
    ((cI c).hom.app L).right =
      (PicardGroupoid.squarePullbackIso T.j₂ c.g₂ c.t S.j₂ c.h₂).hom.app L := rfl

@[simp]
lemma Comp_hom_app_left (c : CubeMap S T) (c' : CubeMap T T') (D : S.GD) :
    ((Comp c c').hom.app D).left =
      (PicardGroupoid.pullbackComp c'.g₁ c.g₁).hom.app D.left := rfl

@[simp]
lemma Comp_hom_app_right (c : CubeMap S T) (c' : CubeMap T T') (D : S.GD) :
    ((Comp c c').hom.app D).right =
      (PicardGroupoid.pullbackComp c'.g₂ c.g₂).hom.app D.right := rfl

@[simp]
lemma C_map_left {L L' : PicardGroupoid T.X} (f : L ⟶ L') :
    (T.C.map f).left = (PicardGroupoid.pullback T.j₁).map f := rfl

@[simp]
lemma C_map_right {L L' : PicardGroupoid T.X} (f : L ⟶ L') :
    (T.C.map f).right = (PicardGroupoid.pullback T.j₂).map f := rfl

/-- The component of `cI` with its clean type. -/
def cIa (c : CubeMap S T) (L : PicardGroupoid S.X) :
    T.C.obj ((P c.t).obj L) ⟶ c.R.obj (S.C.obj L) :=
  (cI c).hom.app L

/-- The component of `Comp` with its clean type. -/
def CompA (c : CubeMap S T) (c' : CubeMap T T') (D : S.GD) :
    c'.R.obj (c.R.obj D) ⟶ (comp c' c).R.obj D :=
  (Comp c c').hom.app D

lemma cIa_left (c : CubeMap S T) (L : PicardGroupoid S.X) :
    (cIa c L).left = sqH T.j₁ c.g₁ c.t S.j₁ c.h₁ L :=
  rfl

lemma cIa_right (c : CubeMap S T) (L : PicardGroupoid S.X) :
    (cIa c L).right = sqH T.j₂ c.g₂ c.t S.j₂ c.h₂ L :=
  rfl

lemma CompA_left (c : CubeMap S T) (c' : CubeMap T T') (D : S.GD) :
    (CompA c c' D).left = pcH c'.g₁ c.g₁ D.left :=
  rfl

lemma CompA_right (c : CubeMap S T) (c' : CubeMap T T') (D : S.GD) :
    (CompA c c' D).right = pcH c'.g₂ c.g₂ D.right :=
  rfl

/-- Pseudonaturality: the comparison of a composite cube is the pasting of the
two comparisons and the composition comparisons. -/
lemma cI_comp (c : CubeMap S T) (c' : CubeMap T T') (L : PicardGroupoid S.X) :
    cIa (comp c' c) L =
      T'.C.map (pcI c'.t c.t L) ≫ cIa c' ((P c.t).obj L) ≫
          c'.R.map (cIa c L) ≫ CompA c c' (S.C.obj L) := by
  apply Comma.hom_ext
  · rw [Comma.comp_left, Comma.comp_left, Comma.comp_left, cIa_left, cIa_left, CompA_left,
      C_map_left, R_map_left, cIa_left]
    exact paste_leg S.j₁ T.j₁ T'.j₁ c.t c.g₁ c'.t c'.g₁ c.h₁ c'.h₁ (comp c' c).h₁ L
  · rw [Comma.comp_right, Comma.comp_right, Comma.comp_right, cIa_right, cIa_right,
      CompA_right, C_map_right, R_map_right, cIa_right]
    exact paste_leg S.j₂ T.j₂ T'.j₂ c.t c.g₂ c'.t c'.g₂ c.h₂ c'.h₂ (comp c' c).h₂ L

@[reassoc]
lemma CompA_nat (c : CubeMap S T) (c' : CubeMap T T') {D D' : S.GD} (f : D ⟶ D') :
    c'.R.map (c.R.map f) ≫ CompA c c' D' = CompA c c' D ≫ (comp c' c).R.map f := by
  apply Comma.hom_ext
  · rw [Comma.comp_left, Comma.comp_left, CompA_left, CompA_left, R_map_left, R_map_left,
      R_map_left]
    exact pcH_nat c'.g₁ c.g₁ f.left
  · rw [Comma.comp_right, Comma.comp_right, CompA_right, CompA_right, R_map_right,
      R_map_right, R_map_right]
    exact pcH_nat c'.g₂ c.g₂ f.right

@[reassoc]
lemma cIa_nat (c : CubeMap S T) {L L' : PicardGroupoid S.X} (a : L ⟶ L') :
    T.C.map ((P c.t).map a) ≫ cIa c L' = cIa c L ≫ c.R.map (S.C.map a) :=
  (cI c).hom.naturality a

/-- Associativity of the composition comparisons of restrictions. -/
lemma Comp_assoc (c : CubeMap S T) (c' : CubeMap T T') (c'' : CubeMap T' T'') (D : S.GD) :
    c''.R.map (CompA c c' D) ≫ CompA (comp c' c) c'' D =
      CompA c' c'' (c.R.obj D) ≫ CompA c (comp c'' c') D ≫
        eqToHom (congrArg (fun e ↦ e.R.obj D) (comp_assoc c c' c'')) := by
  apply Comma.hom_ext
  · rw [Comma.comp_left, Comma.comp_left, Comma.comp_left, R_map_left, CompA_left,
      CompA_left, CompA_left, CompA_left, Comma.eqToHom_left]
    exact pc_assoc c''.g₁ c'.g₁ c.g₁ D.left
  · rw [Comma.comp_right, Comma.comp_right, Comma.comp_right, R_map_right, CompA_right,
      CompA_right, CompA_right, CompA_right, Comma.eqToHom_right]
    exact pc_assoc c''.g₂ c'.g₂ c.g₂ D.right

/-- The component of `cI` as an isomorphism. -/
def cIi (c : CubeMap S T) (L : PicardGroupoid S.X) :
    T.C.obj ((P c.t).obj L) ≅ c.R.obj (S.C.obj L) :=
  (cI c).app L

/-- The component of `Comp` as an isomorphism. -/
def CompI (c : CubeMap S T) (c' : CubeMap T T') (D : S.GD) :
    c'.R.obj (c.R.obj D) ≅ (comp c' c).R.obj D :=
  (Comp c c').app D

@[simp] lemma cIi_hom (c : CubeMap S T) (L : PicardGroupoid S.X) :
    (cIi c L).hom = cIa c L := rfl

@[simp] lemma CompI_hom (c : CubeMap S T) (c' : CubeMap T T') (D : S.GD) :
    (CompI c c' D).hom = CompA c c' D := rfl

end CubeMap

section Realization

open CubeMap

variable {S T T' T'' : Sq.{u}} {D : S.GD}

/-- Pull back a realization of the restricted datum along a further cube. -/
def pb (c : CubeMap S T) (c' : CubeMap T T') {N : PicardGroupoid T.X}
    (ρ : T.C.obj N ≅ c.R.obj D) : T'.C.obj ((P c'.t).obj N) ≅ (comp c' c).R.obj D :=
  cIi c' N ≪≫ c'.R.mapIso ρ ≪≫ CompI c c' D

lemma pb_hom (c : CubeMap S T) (c' : CubeMap T T') {N : PicardGroupoid T.X}
    (ρ : T.C.obj N ≅ c.R.obj D) :
    (pb c c' ρ).hom = cIa c' N ≫ c'.R.map ρ.hom ≫ CompA c c' D := rfl

/-- Pulling back an arrow which respects two realizations respects their pullbacks. -/
lemma pb_respects (c : CubeMap S T) (c' : CubeMap T T') {N₁ N₂ : PicardGroupoid T.X}
    (ρ₁ : T.C.obj N₁ ≅ c.R.obj D) (ρ₂ : T.C.obj N₂ ≅ c.R.obj D) (τ : N₁ ⟶ N₂)
    (h : T.C.map τ ≫ ρ₂.hom = ρ₁.hom) :
    T'.C.map ((P c'.t).map τ) ≫ (pb c c' ρ₂).hom = (pb c c' ρ₁).hom := by
  rw [pb_hom, pb_hom, cIa_nat_assoc, ← Functor.map_comp_assoc, h]

/-- Two successive pullbacks of a realization agree with one pullback along the
composite cube, through the composition comparison. -/
lemma pb_pb (c : CubeMap S T) (c' : CubeMap T T') (c'' : CubeMap T' T'')
    {N : PicardGroupoid T.X} (ρ : T.C.obj N ≅ c.R.obj D) :
    (pb (comp c' c) c'' (pb c c' ρ)).hom =
      T''.C.map (pcH c''.t c'.t N) ≫ (pb c (comp c'' c') ρ).hom ≫
        eqToHom (congrArg (fun e ↦ e.R.obj D) (comp_assoc c c' c'')) := by
  rw [pb_hom, pb_hom, pb_hom, cI_comp c' c'' N]
  simp only [Category.assoc, ← Functor.map_comp_assoc, pcH_pcI, CategoryTheory.Functor.map_id,
    Category.id_comp]
  simp only [Functor.map_comp, Category.assoc]
  rw [← CompA_nat_assoc, Comp_assoc]

end Realization

end Langlands.AlgebraicGeometry.Picard.SquareGluingDescent
