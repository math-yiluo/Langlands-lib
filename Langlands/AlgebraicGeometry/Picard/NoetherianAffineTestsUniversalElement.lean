import Langlands.AlgebraicGeometry.Picard.LineHom.AffineExtension
import Langlands.AlgebraicGeometry.AlgebraicSpace.ProperSchemeCover.OpenGluing

/-! # Universal elements from representability on noetherian affine tests -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace Langlands.AlgebraicGeometry.Picard.NoetherianAffineTests

open AlgebraicSpace AlgebraicSpace.ProperSchemeCover

variable {S : Scheme.{u}}

/-- Two sections of an fppf sheaf that agree on the members of an open cover are equal. -/
lemma eq_of_isOpenCover (F : FppfSheaf S) (T : Over S) {ι : Type*} (U : ι → T.left.Opens)
    (hU : TopologicalSpace.IsOpenCover U) (x y : F.obj.obj (op T))
    (h : ∀ i, F.obj.map (openOverι T (U i)).op x = F.obj.map (openOverι T (U i)).op y) :
    x = y := by
  have hsh := (isSheaf_iff_isSheaf_of_type (fppfTopology S) F.obj).mp F.property
  have hs := (Presieve.isSheafFor_iff_generate (P := F.obj) (Presieve.ofArrows _ _)).mpr
    (hsh _ (openOver_covering T U hU))
  apply hs.isSeparatedFor.ext
  rintro _ _ ⟨i⟩
  exact h i

/-- Affine opens satisfying a property cover a scheme if every point lies in one of them. -/
lemma isOpenCover_affineOpens {X : Scheme.{u}} (Q : X.affineOpens → Prop)
    (hQ : ∀ x : X, ∃ W : X.affineOpens, Q W ∧ x ∈ W.1) :
    TopologicalSpace.IsOpenCover (fun W : {W : X.affineOpens // Q W} ↦ W.1.1) := by
  refine TopologicalSpace.IsOpenCover.mk (eq_top_iff.mpr fun x _ ↦ ?_)
  obtain ⟨W, hW, hx⟩ := hQ x
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨W, hW⟩, hx⟩

/-- Every point of a scheme lies in an affine open inside any given open neighbourhood. -/
lemma exists_affineOpen_le {X : Scheme.{u}} {x : X} {V : X.Opens} (hx : x ∈ V) :
    ∃ W : X.affineOpens, x ∈ W.1 ∧ W.1 ≤ V := by
  obtain ⟨W, hW, hxW, hWV⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
    X.isBasis_affineOpens hx
  exact ⟨⟨W, hW⟩, hxW, hWV⟩

/-- The affine opens of a scheme cover it. -/
lemma isOpenCover_all_affineOpens (X : Scheme.{u}) :
    TopologicalSpace.IsOpenCover (fun W : X.affineOpens ↦ W.1) := by
  refine TopologicalSpace.IsOpenCover.mk (eq_top_iff.mpr fun x _ ↦ ?_)
  obtain ⟨V, hV, -⟩ := exists_affineOpen_le (x := x) (V := ⊤) trivial
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨V, hV⟩

instance isAffine_openOver (T : Over S) (W : T.left.affineOpens) :
    IsAffine (openOver T W.1).left :=
  W.2

instance isNoetherian_openOver (T : Over S) [IsLocallyNoetherian T.left]
    (W : T.left.affineOpens) : IsNoetherian (openOver T W.1).left where
  toIsLocallyNoetherian := inferInstanceAs (IsLocallyNoetherian W.1.toScheme)
  toCompactSpace := inferInstanceAs (CompactSpace (openOver T W.1).left)

instance isLocallyNoetherian_openOver (T : Over S) [IsLocallyNoetherian T.left]
    (W : T.left.Opens) : IsLocallyNoetherian (openOver T W).left :=
  inferInstanceAs (IsLocallyNoetherian W.toScheme)

section Universal

variable {F : FppfSheaf S} {P : Over S}
  (α : (ObjectProperty.ι (fun T : Over S ↦ IsAffine T.left ∧ IsNoetherian T.left)).op ⋙
      yoneda.obj P ⋙ uliftFunctor.{u + 1} ≅
    (ObjectProperty.ι (fun T : Over S ↦ IsAffine T.left ∧ IsNoetherian T.left)).op ⋙ F.obj)

/-- The component of `α` at a noetherian affine test. -/
def aff (T : Over S) [IsAffine T.left] [IsNoetherian T.left] (g : T ⟶ P) :
    F.obj.obj (op T) :=
  α.hom.app (op ⟨T, ⟨inferInstance, inferInstance⟩⟩) (ULift.up.{u + 1} g)

/-- The inverse component of `α` at a noetherian affine test. -/
def affInv (T : Over S) [IsAffine T.left] [IsNoetherian T.left] (x : F.obj.obj (op T)) :
    T ⟶ P :=
  (α.inv.app (op ⟨T, ⟨inferInstance, inferInstance⟩⟩) x).down

lemma aff_comp {T T' : Over S} [IsAffine T.left] [IsNoetherian T.left] [IsAffine T'.left]
    [IsNoetherian T'.left] (b : T' ⟶ T) (g : T ⟶ P) :
    aff α T' (b ≫ g) = F.obj.map b.op (aff α T g) :=
  types_congr_hom (α.hom.naturality (ObjectProperty.homMk
    (P := fun T : Over S => IsAffine T.left ∧ IsNoetherian T.left)
    (X := ⟨T', ⟨inferInstance, inferInstance⟩⟩) (Y := ⟨T, ⟨inferInstance, inferInstance⟩⟩)
      b).op) (ULift.up.{u + 1} g)

lemma aff_affInv (T : Over S) [IsAffine T.left] [IsNoetherian T.left]
    (x : F.obj.obj (op T)) : aff α T (affInv α T x) = x :=
  types_congr_hom (α.inv_hom_id_app (op ⟨T, ⟨inferInstance, inferInstance⟩⟩)) x

lemma affInv_aff (T : Over S) [IsAffine T.left] [IsNoetherian T.left] (g : T ⟶ P) :
    affInv α T (aff α T g) = g :=
  congrArg ULift.down (types_congr_hom
    (α.hom_inv_id_app (op ⟨T, ⟨inferInstance, inferInstance⟩⟩)) (ULift.up.{u + 1} g))

lemma aff_injective (T : Over S) [IsAffine T.left] [IsNoetherian T.left] :
    Function.Injective (aff α T) := fun g g' h ↦ by
  rw [← affInv_aff α T g, h, affInv_aff]

variable [IsLocallyNoetherian P.left]

/-- The sections of `F` on the affine opens of `P` given by `α`. -/
def chartSection (W : P.left.affineOpens) : F.obj.obj (op (openOver P W.1)) :=
  aff α (openOver P W.1) (openOverι P W.1)

lemma chartSection_compatible (W W' : P.left.affineOpens) :
    F.obj.map (openOverHomOfLE P (inf_le_left : W.1 ⊓ W'.1 ≤ W.1)).op (chartSection α W) =
      F.obj.map (openOverHomOfLE P (inf_le_right : W.1 ⊓ W'.1 ≤ W'.1)).op
        (chartSection α W') := by
  let T' := openOver P (W.1 ⊓ W'.1)
  refine eq_of_isOpenCover F T' (fun V : {V : T'.left.affineOpens // True} ↦ V.1.1)
    (isOpenCover_affineOpens _ fun x ↦ ?_) _ _ fun V ↦ ?_
  · obtain ⟨V, hV, -⟩ := exists_affineOpen_le (x := x) (V := ⊤) trivial
    exact ⟨V, trivial, hV⟩
  · simp only [chartSection]
    rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp,
      ← aff_comp, ← aff_comp, Category.assoc, Category.assoc, openOverHomOfLE_ι,
      openOverHomOfLE_ι]

/-- The universal section of `F` over `P`, glued from the affine charts. -/
lemma exists_universal :
    ∃ ξ : F.obj.obj (op P), ∀ W : P.left.affineOpens,
      F.obj.map (openOverι P W.1).op ξ = chartSection α W :=
  exists_glue F P (fun W : P.left.affineOpens ↦ W.1) (isOpenCover_all_affineOpens P.left)
    (chartSection α) (chartSection_compatible α)

/-- A universal section restricts to `α` along every morphism from a noetherian affine test. -/
lemma map_universal {ξ : F.obj.obj (op P)}
    (hξ : ∀ W : P.left.affineOpens, F.obj.map (openOverι P W.1).op ξ = chartSection α W)
    (T : Over S) [IsAffine T.left] [IsNoetherian T.left] (g : T ⟶ P) :
    F.obj.map g.op ξ = aff α T g := by
  let Q : T.left.affineOpens → Prop := fun V ↦ ∃ W : P.left.affineOpens, V.1 ≤ g.left ⁻¹ᵁ W.1
  refine eq_of_isOpenCover F T (fun V : {V : T.left.affineOpens // Q V} ↦ V.1.1)
    (isOpenCover_affineOpens Q fun x ↦ ?_) _ _ fun V ↦ ?_
  · obtain ⟨W, hW, -⟩ := exists_affineOpen_le (x := g.left x) (V := ⊤) trivial
    obtain ⟨V, hxV, hVW⟩ := exists_affineOpen_le (x := x) (V := g.left ⁻¹ᵁ W.1) hW
    exact ⟨V, ⟨W, hVW⟩, hxV⟩
  · obtain ⟨V, W, hVW⟩ := V
    let c : openOver T V.1 ⟶ openOver P W.1 :=
      Over.homMk (g.left.resLE W.1 V.1 hVW) (by
        simp only [openOver, Over.mk_hom]
        rw [Scheme.Hom.resLE_comp_ι_assoc, Over.w g])
    have hc : c ≫ openOverι P W.1 = openOverι T V.1 ≫ g := by
      apply Over.OverMorphism.ext
      simp [c, Scheme.Hom.resLE_comp_ι]
    change F.obj.map (openOverι T V.1).op (F.obj.map g.op ξ) =
      F.obj.map (openOverι T V.1).op (aff α T g)
    rw [← Functor.map_comp_apply, ← op_comp, ← hc, op_comp, Functor.map_comp_apply, hξ,
      chartSection, ← aff_comp, ← aff_comp, hc]

/-- There is a section of `F` over `P` restricting to `α` along every morphism from a noetherian
affine test. -/
lemma exists_universal_map :
    ∃ ξ : F.obj.obj (op P), ∀ (T : Over S) [IsAffine T.left] [IsNoetherian T.left] (g : T ⟶ P),
      F.obj.map g.op ξ = aff α T g := by
  obtain ⟨ξ, hξ⟩ := exists_universal α
  exact ⟨ξ, fun T _ _ g ↦ map_universal α hξ T g⟩

end Universal

/-- A section of an fppf sheaf over `P` whose pullbacks along the morphisms from each affine test
to `P` are bijective represents the sheaf. -/
def representableByOfBijectiveAffine (F : FppfSheaf S) (P : Over S) (ξ : F.obj.obj (op P))
    (h : ∀ T : Over S, IsAffine T.left →
      Function.Bijective (fun g : T ⟶ P ↦ F.obj.map g.op ξ)) :
    F.obj.RepresentableBy P :=
  let Ψ : (schemeYoneda S).obj P ⟶ F.obj := uliftYonedaEquiv.symm ξ
  haveI : IsIso Ψ := LineHom.isIso_of_bijective_affine ((schemeSheaf S).obj P).property
    F.property Ψ fun T hT ↦ (h T hT).comp Equiv.ulift.bijective
  (Functor.RepresentableBy.equivUliftYonedaIso F.obj P).symm (asIso Ψ)

@[simp]
lemma representableByOfBijectiveAffine_homEquiv (F : FppfSheaf S) (P : Over S)
    (ξ : F.obj.obj (op P))
    (h : ∀ T : Over S, IsAffine T.left →
      Function.Bijective (fun g : T ⟶ P ↦ F.obj.map g.op ξ)) {T : Over S} (g : T ⟶ P) :
    (representableByOfBijectiveAffine F P ξ h).homEquiv g = F.obj.map g.op ξ :=
  rfl

end Langlands.AlgebraicGeometry.Picard.NoetherianAffineTests
