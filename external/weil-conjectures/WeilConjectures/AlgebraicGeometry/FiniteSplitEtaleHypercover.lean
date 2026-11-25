/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.AlgebraicTopology.SimplicialObject.Homotopy
public import Mathlib.AlgebraicTopology.SimplicialObject.Split

/-!
# Blueprint statements

corollary-cohomology-pro-etale-affine.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- corollary-cohomology-pro-etale-affine. -/
structure SplitEtaleHypercover (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] where
  simplicial : SimplicialObject X.Etale
  splitting : simplicial.Splitting
  matching : ℕ → X.Etale
  projection : ∀ (n : ℕ) (Δ : SimplexCategory), Δ.len < n →
    (Δ ⟶ SimplexCategory.mk n) → (matching n ⟶ simplicial.obj (op Δ))
  projection_naturality : ∀ (n : ℕ) (Δ Δ' : SimplexCategory)
    (h : Δ.len < n) (h' : Δ'.len < n) (α : Δ' ⟶ Δ)
    (θ : Δ ⟶ SimplexCategory.mk n),
    projection n Δ h θ ≫ simplicial.map α.op = projection n Δ' h' (α ≫ θ)
  matching_universal : ∀ (n : ℕ) (T : Over X)
    (p : ∀ (Δ : SimplexCategory), Δ.len < n → (Δ ⟶ SimplexCategory.mk n) →
      (T ⟶ (Scheme.Etale.forget X).obj (simplicial.obj (op Δ)))),
    (∀ (Δ Δ' : SimplexCategory) (h : Δ.len < n) (h' : Δ'.len < n)
      (α : Δ' ⟶ Δ) (θ : Δ ⟶ SimplexCategory.mk n),
      p Δ h θ ≫ (Scheme.Etale.forget X).map (simplicial.map α.op) =
        p Δ' h' (α ≫ θ)) →
    ∃! f : T ⟶ (Scheme.Etale.forget X).obj (matching n),
      ∀ (Δ : SimplexCategory) (h : Δ.len < n) (θ : Δ ⟶ SimplexCategory.mk n),
        f ≫ (Scheme.Etale.forget X).map (projection n Δ h θ) = p Δ h θ
  matchingMap : ∀ n, simplicial.obj (op (SimplexCategory.mk n)) ⟶ matching n
  matchingMap_projection : ∀ (n : ℕ) (Δ : SimplexCategory) (h : Δ.len < n)
    (θ : Δ ⟶ SimplexCategory.mk n),
    matchingMap n ≫ projection n Δ h θ = simplicial.map θ.op
  matching_cover : ∀ n, Surjective (matchingMap n).left

/-- corollary-cohomology-pro-etale-affine. -/
structure FiniteSplitEtaleHypercover (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] extends SplitEtaleHypercover X where
  finite_each_degree : ∀ n, ∃ (k : ℕ) (V : Fin k → X.Etale)
    (ι : ∀ i, V i ⟶ splitting.N n),
    Nonempty (IsColimit (Cofan.mk (splitting.N n) ι)) ∧
      ∀ i, CompactSpace (V i).left ∧ QuasiSeparatedSpace (V i).left ∧
        LocallyOfFinitePresentation (V i).hom ∧ QuasiCompact (V i).hom ∧
          QuasiSeparated (V i).hom

namespace FiniteSplitEtaleHypercover

variable {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]

/-- corollary-cohomology-pro-etale-affine. -/
abbrev Refinement (U V : FiniteSplitEtaleHypercover X) := U.simplicial ⟶ V.simplicial

/-- corollary-cohomology-pro-etale-affine. -/
def isRefinementHomotopic {U V : FiniteSplitEtaleHypercover X}
    (f g : U.Refinement V) : Prop :=
  Relation.EqvGen (fun a b : U.Refinement V ↦ Nonempty (SimplicialObject.Homotopy a b)) f g

/-- corollary-cohomology-pro-etale-affine. -/
def RefinementClasses (U V : FiniteSplitEtaleHypercover X) :=
  Quot (fun a b : U.Refinement V ↦ Nonempty (SimplicialObject.Homotopy a b))

/-- corollary-cohomology-pro-etale-affine. -/
def truncation (U : FiniteSplitEtaleHypercover X) (r : ℕ) :=
  ((SimplicialObject.truncation r).obj U.simplicial,
    fun n : Fin (r + 1) ↦
      (U.splitting.N n.val, U.splitting.cofan (op (SimplexCategory.mk n.val)),
        U.splitting.isColimit' (op (SimplexCategory.mk n.val)),
        PLift.up (U.finite_each_degree n.val),
        U.matching n.val, U.matchingMap n.val, U.projection n.val,
        PLift.up (U.projection_naturality n.val), PLift.up (U.matching_universal n.val),
        PLift.up (U.matchingMap_projection n.val), PLift.up (U.matching_cover n.val)))

/-- corollary-cohomology-pro-etale-affine. -/
def sectionCosimplicial (U : FiniteSplitEtaleHypercover X)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{v}) : CosimplicialObject AddCommGrpCat.{v} :=
  U.simplicial.rightOp ⋙ F.obj

/-- corollary-cohomology-pro-etale-affine. -/
noncomputable def complex (U : FiniteSplitEtaleHypercover X)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{v}) : CochainComplex AddCommGrpCat.{v} ℕ :=
  (AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{v}).obj
    (U.sectionCosimplicial F)

/-- corollary-cohomology-pro-etale-affine. -/
noncomputable def cohomology (U : FiniteSplitEtaleHypercover X)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{v}) (q : ℕ) : AddCommGrpCat.{v} :=
  (U.complex F).homology q

end FiniteSplitEtaleHypercover

/-- corollary-cohomology-pro-etale-affine. -/
structure TruncatedFiniteSplitEtaleHypercover (X : Scheme.{u}) (r : ℕ) where
  simplicial : SimplicialObject.Truncated X.Etale r
  N : Fin (r + 1) → X.Etale
  inclusion : ∀ n, N n ⟶ simplicial.obj (op ⟨SimplexCategory.mk n.val,
    Nat.le_of_lt_succ n.isLt⟩)
  splitting : ∀ Δ : (SimplexCategory.Truncated r)ᵒᵖ,
    IsColimit (Cofan.mk (simplicial.obj Δ)
      (fun a : Σ m : Fin (r + 1),
          {α : Δ.unop.obj ⟶ SimplexCategory.mk m.val // Epi α} ↦
        inclusion a.1 ≫ simplicial.map (SimplexCategory.Truncated.Hom.tr a.2.val Δ.unop.property
          (Nat.le_of_lt_succ a.1.isLt)).op))
  finite_each_degree : ∀ n, ∃ (k : ℕ) (V : Fin k → X.Etale)
    (ι : ∀ i, V i ⟶ N n),
    Nonempty (IsColimit (Cofan.mk (N n) ι)) ∧
      ∀ i, CompactSpace (V i).left ∧ QuasiSeparatedSpace (V i).left ∧
        LocallyOfFinitePresentation (V i).hom ∧ QuasiCompact (V i).hom ∧
          QuasiSeparated (V i).hom
  matching : Fin (r + 1) → X.Etale
  projection : ∀ (n : Fin (r + 1)) (Δ : SimplexCategory.Truncated r),
    Δ.obj.len < n.val → (Δ.obj ⟶ SimplexCategory.mk n.val) →
      (matching n ⟶ simplicial.obj (op Δ))
  projection_naturality : ∀ (n : Fin (r + 1)) (Δ Δ' : SimplexCategory.Truncated r)
    (h : Δ.obj.len < n.val) (h' : Δ'.obj.len < n.val) (α : Δ' ⟶ Δ)
    (θ : Δ.obj ⟶ SimplexCategory.mk n.val),
    projection n Δ h θ ≫ simplicial.map α.op =
      projection n Δ' h' (α.hom ≫ θ)
  matching_universal : ∀ (n : Fin (r + 1)) (T : Over X)
    (p : ∀ (Δ : SimplexCategory.Truncated r), Δ.obj.len < n.val →
      (Δ.obj ⟶ SimplexCategory.mk n.val) →
        (T ⟶ (Scheme.Etale.forget X).obj (simplicial.obj (op Δ)))),
    (∀ (Δ Δ' : SimplexCategory.Truncated r)
      (h : Δ.obj.len < n.val) (h' : Δ'.obj.len < n.val) (α : Δ' ⟶ Δ)
      (θ : Δ.obj ⟶ SimplexCategory.mk n.val),
      p Δ h θ ≫ (Scheme.Etale.forget X).map (simplicial.map α.op) =
        p Δ' h' (α.hom ≫ θ)) →
    ∃! f : T ⟶ (Scheme.Etale.forget X).obj (matching n),
      ∀ (Δ : SimplexCategory.Truncated r) (h : Δ.obj.len < n.val)
        (θ : Δ.obj ⟶ SimplexCategory.mk n.val),
        f ≫ (Scheme.Etale.forget X).map (projection n Δ h θ) = p Δ h θ
  matchingMap : ∀ n : Fin (r + 1),
    simplicial.obj (op ⟨SimplexCategory.mk n.val, Nat.le_of_lt_succ n.isLt⟩) ⟶ matching n
  matchingMap_projection : ∀ (n : Fin (r + 1)) (Δ : SimplexCategory.Truncated r)
    (h : Δ.obj.len < n.val) (θ : Δ.obj ⟶ SimplexCategory.mk n.val),
    matchingMap n ≫ projection n Δ h θ =
      simplicial.map (SimplexCategory.Truncated.Hom.tr θ Δ.property
        (Nat.le_of_lt_succ n.isLt)).op
  matching_cover : ∀ n, Surjective (matchingMap n).left

namespace TruncatedFiniteSplitEtaleHypercover

/-- corollary-cohomology-pro-etale-affine. -/
def diagram {X : Scheme.{u}} {r : ℕ} (U : TruncatedFiniteSplitEtaleHypercover X r) :=
  U.simplicial ⋙ Scheme.Etale.forget X

/-- corollary-cohomology-pro-etale-affine. -/
def IsBaseChange {X Y : Scheme.{u}} {r : ℕ} (f : X ⟶ Y)
    (U : TruncatedFiniteSplitEtaleHypercover Y r)
    (V : TruncatedFiniteSplitEtaleHypercover X r) : Prop :=
  ∃ e : U.diagram ⋙ Over.pullback f ≅ V.diagram,
    ∀ n : Fin (r + 1),
      ∃ a : (Over.pullback f).obj ((Scheme.Etale.forget Y).obj (U.N n)) ≅
          (Scheme.Etale.forget X).obj (V.N n),
        (Over.pullback f).map ((Scheme.Etale.forget Y).map (U.inclusion n)) ≫
            e.hom.app (op ⟨SimplexCategory.mk n.val, Nat.le_of_lt_succ n.isLt⟩) =
          a.hom ≫ (Scheme.Etale.forget X).map (V.inclusion n)

end TruncatedFiniteSplitEtaleHypercover
end AlgebraicGeometry
