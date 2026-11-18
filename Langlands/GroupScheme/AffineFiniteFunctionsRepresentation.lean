import Langlands.GroupScheme.AffineLinearEmbeddingCorepresentedProof

/-! # Finite sets of functions in a finite-dimensional representation -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace Corepresented

open LinearEmbedding

/-- A finite subset of an arbitrary representing algebra is contained in the
image of the coordinate map of one actual finite-dimensional representation. -/
theorem exists_representation_containing (k : Type u) [Field k]
    {F : CommAlgCat.{u} (CommRingCat.of k) ⥤ GrpCat.{u}}
    {B : CommAlgCat.{u} (CommRingCat.of k)}
    (e : (F ⋙ forget GrpCat).CorepresentableBy B) (s : Finset B) :
    ∃ (n : ℕ) (ρ : groupScheme F e ⟶ GeneralLinear.groupScheme (Fin n) (CommRingCat.of k))
      (φ : GeneralLinear.CoordinateRing (Fin n) (CommRingCat.of k) →ₐ[CommRingCat.of k] B),
      ρ.hom.hom.left = Spec.map (CommRingCat.ofHom φ.toRingHom) ∧
      ∀ x ∈ s, x ∈ φ.range := by
  classical
  obtain ⟨n, a, hmul, hone, hspan⟩ :=
    Comodule.exists_matrix (coassoc e) (leftCounit e) (rightCounit e) s
  let α := toGL e a hmul hone
  let ρ := groupSchemeMap e (GeneralLinear.corepresentableBy (Fin n) (CommRingCat.of k)) α
  let g : GL (Fin n) B := α.app B (e.homEquiv (𝟙 B))
  let φ : GeneralLinear.CoordinateRing (Fin n) (CommRingCat.of k) →ₐ[CommRingCat.of k] B :=
    GeneralLinear.classify g
  have hg : ∀ i j, (g : Matrix (Fin n) (Fin n) B) i j = a i j := by
    intro i j
    change (cls e (pt e (𝟙 B))).hom.mapMatrix a i j = a i j
    rw [cls_pt]
    rfl
  have hcoeff : ∀ i j, a i j ∈ φ.range := by
    intro i j
    exact ⟨_, (GeneralLinear.classify_entry g i j).trans (hg i j)⟩
  have hle : Submodule.span (CommRingCat.of k)
      (Set.range fun p : Fin n × Fin n => a p.1 p.2) ≤ φ.range.toSubmodule := by
    rw [Submodule.span_le]
    rintro _ ⟨⟨i, j⟩, rfl⟩
    exact hcoeff i j
  exact ⟨n, ρ, φ, rfl, fun x hx => hle (hspan x hx)⟩

end Corepresented

/-- One finite-dimensional representation whose actual coordinate pullback
contains a prescribed finite set of global functions. -/
structure FiniteFunctionsRepresentation {k : Type u} [Field k]
    (Q : GroupScheme (Spec (CommRingCat.of k))) (s : Finset Γ(Q.X.left, ⊤)) where
  dimension : ℕ
  hom : Q ⟶ GeneralLinear.groupScheme (Fin dimension) (CommRingCat.of k)
  contains : ∀ x ∈ s, x ∈ Set.range hom.hom.hom.left.appTop.hom

/-- Finite-dimensional representations capture any prescribed finite set of
functions on an affine field group, without a finite-type hypothesis. -/
def finiteFunctionsRepresentation {k : Type u} [Field k]
    (Q : GroupScheme (Spec (CommRingCat.of k))) [IsAffine Q.X.left]
    (s : Finset Γ(Q.X.left, ⊤)) : FiniteFunctionsRepresentation Q s := Classical.choice (by
  classical
  obtain ⟨W, ⟨ψ⟩⟩ := (essImage_algSpec (G := Q.X)).mpr inferInstance
  let B := W.unop
  let r : Γ(Q.X.left, ⊤) ⟶ CommRingCat.of B :=
    ψ.hom.left.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).hom
  let t : Finset B := s.image r.hom
  obtain ⟨n, ρ, φ, hρ, hφ⟩ := Corepresented.exists_representation_containing k
    (AffineCorepresentation.corep Q ψ) t
  let σ : Q ⟶ GeneralLinear.groupScheme (Fin n) (CommRingCat.of k) :=
    AffineCorepresentation.toModel Q ψ ≫ ρ
  have hσ : σ.hom.hom.left = ψ.inv.left ≫ ρ.hom.hom.left := rfl
  have hr : Function.Injective r.hom := by
    have : IsIso ψ.hom.left := inferInstanceAs (IsIso ((Over.forget _).map ψ.hom))
    have : IsIso ψ.hom.left.appTop := Scheme.Γ.map_isIso ψ.hom.left.op
    have : IsIso r := inferInstanceAs (IsIso
      (ψ.hom.left.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).hom))
    exact (ConcreteCategory.bijective_of_isIso r).1
  refine ⟨{ dimension := n, hom := σ, contains := ?_ }⟩
  intro x hx
  obtain ⟨c, hc⟩ := hφ (r.hom x) (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of (GeneralLinear.CoordinateRing (Fin n)
    (CommRingCat.of k)))).inv.hom c, hr ?_⟩
  rw [hσ, Scheme.Hom.comp_appTop]
  change (ρ.hom.hom.left.appTop ≫ ψ.inv.left.appTop ≫ ψ.hom.left.appTop ≫
    (Scheme.ΓSpecIso (CommRingCat.of B)).hom).hom _ = r.hom x
  have hψ : ψ.inv.left.appTop ≫ ψ.hom.left.appTop = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop]
    have he : ψ.hom.left ≫ ψ.inv.left = 𝟙 _ := by
      exact congrArg (fun f => f.left) ψ.hom_inv_id
    rw [he]
    rfl
  rw [hρ]
  rw [← Category.assoc, ← Category.assoc,
    Category.assoc (Spec.map (CommRingCat.ofHom φ.toRingHom)).appTop,
    hψ]
  change ((Spec.map (CommRingCat.ofHom φ.toRingHom)).appTop ≫
    (Scheme.ΓSpecIso (CommRingCat.of B)).hom).hom _ = r.hom x
  rw [Scheme.ΓSpecIso_naturality]
  change ((Scheme.ΓSpecIso _).inv ≫ (Scheme.ΓSpecIso _).hom ≫
    CommRingCat.ofHom φ.toRingHom).hom c = _
  rw [Iso.inv_hom_id_assoc]
  exact hc)

end Langlands.GroupScheme
