import Langlands.GroupScheme.MatrixRepresentation.CompositionFactors
import Langlands.GroupScheme.MatrixRepresentation.RationalStableCoordinates
import Langlands.GroupScheme.AlgebraicallyClosedComponentProof

/-! # Intertwiners from the identity component and rational points -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.IdentityComponent

variable {k : Type u} [Field k]
  {G H : GroupScheme (Spec (CommRingCat.of k))}

/-- A rational translate of an actual identity-component inclusion. -/
def componentTranslate (i : H ⟶ G) (g : rationalPoints G) : H.X ⟶ G.X :=
  i.hom.hom ≫ (SchemeAction.translationIso (ModObj.regular G.X) g).hom

instance (i : H ⟶ G) [IsOpenImmersion i.hom.hom.left] (g : rationalPoints G) :
    IsOpenImmersion (componentTranslate i g).left := by
  let e := SchemeAction.translationIso (ModObj.regular G.X) g
  let : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  change IsOpenImmersion (i.hom.hom.left ≫ e.hom.left)
  infer_instance

/-- Over an algebraically closed field, rational translates of the open identity
component cover every point, including the nonreduced scheme structure. -/
def componentTranslateCover [IsAlgClosed k] [LocallyOfFiniteType G.X.hom]
    (i : H ⟶ G) [IsOpenImmersion i.hom.hom.left]
    (hi : Set.range i.hom.hom.left = identitySet G) : G.X.left.OpenCover where
  I₀ := rationalPoints G
  X _ := H.X.left
  f g := (componentTranslate i g).left
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun p => ?_, fun g => inferInstance⟩
    obtain ⟨g, hg⟩ := pointComponent_surjective_of_isAlgClosed G
      (_root_.ConnectedComponents.mk p)
    let e := SchemeAction.translationIso (ModObj.regular G.X) g
    let q := e.inv.left p
    have hq : q ∈ identitySet G := by
      have h := congrArg (translationComponents G g⁻¹) hg
      rw [translationComponents_pointComponent, inv_mul_cancel] at h
      have h' : _root_.ConnectedComponents.mk q =
          _root_.ConnectedComponents.mk (identityPoint G) := h.symm
      exact _root_.ConnectedComponents.coe_eq_coe'.mp h'
    have hq' : q ∈ Set.range i.hom.hom.left := hi.symm ▸ hq
    obtain ⟨y, hy⟩ := hq'
    refine ⟨g, y, ?_⟩
    change e.hom.left (i.hom.hom.left y) = p
    rw [hy]
    exact congrArg (fun a : G.X ⟶ G.X => a.left p) e.inv_hom_id

end Langlands.GroupScheme.IdentityComponent

namespace Langlands.GroupScheme.MatrixRepresentation

variable {k : Type u} [Field k]
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- An actual intertwiner can be checked at the universal scheme point. -/
theorem intertwines_iff_universal_pointMatrix [IsAffineHom G.X.hom]
    (ρ : MatrixRepresentation G n) (σ : MatrixRepresentation G m) (C : Matrix m n k) :
    Intertwines ρ σ C ↔
      C.map (scalarMap G.X) * (ρ.pointMatrix G.X (𝟙 _) : Matrix n n Γ(G.X.left, ⊤)) =
        (σ.pointMatrix G.X (𝟙 _) : Matrix m m Γ(G.X.left, ⊤)) * C.map (scalarMap G.X) := by
  constructor
  · exact fun h => h.pointMatrix G.X (𝟙 _)
  · intro h
    have hT (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ G.X) :
        C.map (scalarMap T) * (ρ.pointMatrix T x : Matrix n n Γ(T.left, ⊤)) =
          (σ.pointMatrix T x : Matrix m m Γ(T.left, ⊤)) * C.map (scalarMap T) := by
      have hx := congrArg (fun M : Matrix m n Γ(G.X.left, ⊤) =>
        M.map x.left.appTop.hom) h
      have hC : (C.map (scalarMap G.X)).map x.left.appTop.hom =
          C.map (scalarMap T) := by
        ext r s
        exact scalarMap_comp x _
      have hM {l : Type} [Fintype l] [DecidableEq l] (τ : MatrixRepresentation G l) :
          (τ.pointMatrix G.X (𝟙 _) : Matrix l l Γ(G.X.left, ⊤)).map x.left.appTop.hom =
            (τ.pointMatrix T x : Matrix l l Γ(T.left, ⊤)) := by
        have h' := congrArg Units.val (τ.pointMatrix_naturality x (𝟙 _))
        change (τ.pointMatrix T (x ≫ 𝟙 _) : Matrix l l Γ(T.left, ⊤)) =
          (τ.pointMatrix G.X (𝟙 _) : Matrix l l Γ(G.X.left, ⊤)).map
            x.left.appTop.hom at h'
        simpa only [Category.comp_id] using h'.symm
      simpa only [Matrix.map_mul, hC, hM] using hx
    intro A x
    let e := Corepresented.affineSectionsAlgEquiv A
    have hx := congrArg (fun M : Matrix m n
      Γ(((algSpec (CommRingCat.of k)).obj (op A)).left, ⊤) => M.map e.toRingHom)
      (hT _ x)
    have hC : (C.map (scalarMap ((algSpec (CommRingCat.of k)).obj (op A)))).map
        e.toRingHom = C.map (algebraMap k A) := by
      ext r s
      exact e.commutes _
    have hM {l : Type} [Fintype l] [DecidableEq l] (τ : MatrixRepresentation G l) :
        (τ.pointMatrix ((algSpec (CommRingCat.of k)).obj (op A)) x :
          Matrix l l Γ(((algSpec (CommRingCat.of k)).obj (op A)).left, ⊤)).map
            e.toRingHom = (τ.affineMatrix A x : Matrix l l A) := by
      rw [pointMatrix_eq_affineMatrix]
      ext r s
      exact e.apply_symm_apply _
    erw [Matrix.map_mul (f := e.toRingHom), Matrix.map_mul (f := e.toRingHom),
      hC, hM, hM] at hx
    exact hx

/-- Identity-component equivariance and equivariance under every rational point
detect actual equivariance over an algebraically closed field, even for
nonreduced groups. -/
theorem intertwines_of_identityComponent_and_rationalMatrix
    [IsAlgClosed k] [LocallyOfFiniteType G.X.hom]
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
    (i : H ⟶ G) [IsOpenImmersion i.hom.hom.left]
    (hi : Set.range i.hom.hom.left = IdentityComponent.identitySet G)
    (ρ : MatrixRepresentation G n) (σ : MatrixRepresentation G m) (C : Matrix m n k)
    (hH : Intertwines (ρ.restrict i) (σ.restrict i) C)
    (hr : ∀ g : rationalPoints G,
      C * (ρ.rationalMatrix g : Matrix n n k) =
        (σ.rationalMatrix g : Matrix m m k) * C) :
    Intertwines ρ σ C := by
  apply (intertwines_iff_universal_pointMatrix ρ σ C).mpr
  have hH' := hH.pointMatrix H.X (𝟙 _)
  simp only [pointMatrix_restrict, Category.id_comp] at hH'
  have hlocal (g : rationalPoints G) :
      C.map (scalarMap H.X) *
          (ρ.pointMatrix H.X (IdentityComponent.componentTranslate i g) :
            Matrix n n Γ(H.X.left, ⊤)) =
        (σ.pointMatrix H.X (IdentityComponent.componentTranslate i g) :
          Matrix m m Γ(H.X.left, ⊤)) * C.map (scalarMap H.X) := by
    have ht : IdentityComponent.componentTranslate i g =
        (toUnit H.X ≫ g) * i.hom.hom := by
      rw [IdentityComponent.componentTranslate, SchemeAction.translationIso,
        SchemeAction.comp_translation]
      rfl
    have hg := congrArg (fun M : Matrix m n k => M.map (scalarMap H.X)) (hr g)
    simp only [Matrix.map_mul] at hg
    simp only [ht, map_mul, Matrix.GeneralLinearGroup.coe_mul, pointMatrix_constant]
    change C.map (scalarMap H.X) *
        ((ρ.rationalMatrix g : Matrix n n k).map (scalarMap H.X) *
          (ρ.pointMatrix H.X i.hom.hom : Matrix n n Γ(H.X.left, ⊤))) =
      ((σ.rationalMatrix g : Matrix m m k).map (scalarMap H.X) *
        (σ.pointMatrix H.X i.hom.hom : Matrix m m Γ(H.X.left, ⊤))) *
        C.map (scalarMap H.X)
    rw [← Matrix.mul_assoc, hg, Matrix.mul_assoc, hH', ← Matrix.mul_assoc]
  ext r s
  apply Scheme.OpenCover.ext_elem _ _ (IdentityComponent.componentTranslateCover i hi)
  intro g
  let a := IdentityComponent.componentTranslate i g
  have hC : (C.map (scalarMap G.X)).map a.left.appTop.hom =
      C.map (scalarMap H.X) := by
    ext r s
    exact scalarMap_comp a _
  have hM {l : Type} [Fintype l] [DecidableEq l] (τ : MatrixRepresentation G l) :
      (τ.pointMatrix G.X (𝟙 _) : Matrix l l Γ(G.X.left, ⊤)).map a.left.appTop.hom =
        (τ.pointMatrix H.X a : Matrix l l Γ(H.X.left, ⊤)) := by
    have h' := congrArg Units.val (τ.pointMatrix_naturality a (𝟙 _))
    change (τ.pointMatrix H.X (a ≫ 𝟙 _) : Matrix l l Γ(H.X.left, ⊤)) =
      (τ.pointMatrix G.X (𝟙 _) : Matrix l l Γ(G.X.left, ⊤)).map
        a.left.appTop.hom at h'
    simpa only [Category.comp_id] using h'.symm
  change (((C.map (scalarMap G.X) *
    (ρ.pointMatrix G.X (𝟙 _) : Matrix n n Γ(G.X.left, ⊤))).map a.left.appTop.hom) r s) =
      ((((σ.pointMatrix G.X (𝟙 _) : Matrix m m Γ(G.X.left, ⊤)) *
        C.map (scalarMap G.X)).map a.left.appTop.hom) r s)
  simpa only [Matrix.map_mul, hC, hM] using congrArg (fun M => M r s) (hlocal g)

end Langlands.GroupScheme.MatrixRepresentation
