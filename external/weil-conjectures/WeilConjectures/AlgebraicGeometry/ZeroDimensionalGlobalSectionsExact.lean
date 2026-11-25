/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Topology.KrullDimension
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Artinian
import WeilConjectures.Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Products
import WeilConjectures.AlgebraicGeometry.ZeroDimensionalEtaleCohomologyIso
import WeilConjectures.AlgebraicGeometry.ReductionUniversalHomeomorphism
import WeilConjectures.AlgebraicGeometry.StrictlyHenselianSectionsStalk
import WeilConjectures.AlgebraicGeometry.UniversalHomeomorphismInvariance

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry

/-- Global sections of abelian étale sheaves on a zero-dimensional finite-type scheme
 over an algebraically closed field preserve finite colimits.

Source: literature/blueprint/master/blueprint/sec-curve-estimates/lem-sc-arbitrary-curve-cd/
lem-weil-pbc-zero-dimensional-cohomology.md, both proof paragraphs;
Stacks Project, Tags 00KH, 00FV, 054M, 03SI and 03QO.
(blueprint: zero-dimensional-global-sections-exact).

Proof: The finite-type dimension-zero theorem makes the underlying space finite and
 discrete. Pass to the reduction, a universal homeomorphism by Tag 054M; its étale
 sheaf category is exactly equivalent to that of C by Tag 03SI, compatibly with
 global sections. The reduction remains finite type over k. Each open-and-closed
 singleton is affine, reduced, and has a unique prime. Its coordinate ring is a
 field: its nilradical is zero and its unique prime is maximal. The residue field
 theorem (Tag 00FV) identifies that field with k. Thus the reduction is the finite
 coproduct of these spectra, including the empty coproduct when C is empty.
 Sheaves on this coproduct are families of sheaves on Spec k. An algebraically
 closed field is strictly henselian. Apply
 `lem-weil-pbc-strictly-henselian-sections-stalk` (Tag 03QO) to R = k and the identity
 geometric point. Its natural germ isomorphism identifies sections on each summand
 with its geometric stalk. Restriction of global sections to the terminal etale
 object is a natural isomorphism. By `prop-weil-pbc-geometric-stalks-exact`, this
 stalk functor preserves finite colimits, hence so do global sections on each
 summand. Consequently global sections are naturally the finite product of these
 exact stalk functors. Finite products of abelian groups are finite biproducts and
 preserve finite colimits. Transport this fact through the exact sheaf equivalence
 for reduction. This proves the displayed finite-colimit preservation; global
 sections already preserve finite limits as a right adjoint. -/
theorem zero_dimensional_global_sections_preservesFiniteColimits
    (k : Type u) [Field k] [IsAlgClosed k] (C : Scheme.{u})
    (f : C ⟶ Spec (.of k)) [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] (hdim : topologicalKrullDim C ≤ 0) :
    PreservesFiniteColimits (Sheaf.Γ C.smallEtaleTopology AddCommGrpCat.{u + 1}) := by
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace f
  have : IsLocallyArtinian C := IsLocallyArtinian.of_topologicalKrullDim_le_zero hdim
  have : Finite C := finite_of_compact_of_discrete
  let s (x : C) := pointOfClosedPoint f x (isClosed_discrete {x})
  let T (x : C) := (Scheme.pointSmallEtale (s x)).sheafFiber
    (A := AddCommGrpCat.{u + 1})
  let G := Sheaf.Γ C.smallEtaleTopology AddCommGrpCat.{u + 1}
  let c (F : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    F.ΓRes (Opposite.op (Scheme.Etale.mk (𝟙 C))) ≫ Pi.lift (fun x : C ↦
      (Scheme.pointSmallEtale (s x)).toPresheafFiber (Scheme.Etale.mk (𝟙 C))
        (Over.homMk (s x) (Category.comp_id _)) F.obj)
  have hc (F : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}) : IsIso (c F) := by
    have h := zero_dimensional_etale_cohomology_iso k C f hdim F (fun _ ↦ k) s
      (fun x ↦ pointOfClosedPoint_apply f x (isClosed_discrete {x}) _)
    let a := (Functor.homologyRightDerivedFunctorObjSingleFunctorIso G F 0).hom
    let b := (Functor.rightDerivedZeroIsoSelf G).hom.app F
    have : IsIso (a ≫ b ≫ c F) := by simpa only [a, b, c, Category.assoc] using h
    have : IsIso (b ≫ c F) := IsIso.of_isIso_comp_left a (b ≫ c F)
    exact IsIso.of_isIso_comp_left b (c F)
  let e : G ≅ ∏ᶜ T := NatIso.ofComponents
    (fun F ↦ asIso (c F ≫ (piObjIso T F).inv)) (by
      intro F F' φ
      dsimp
      rw [piObj_map]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      apply (cancel_mono (piObjIso T F').hom).1
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      apply Pi.hom_ext
      intro x
      dsimp [G, T, GrothendieckTopology.Point.sheafFiber]
      simp only [c, Category.assoc, Pi.lift_comp_π, Pi.map_π, Pi.lift_comp_π_assoc]
      rw [← Category.assoc, Sheaf.ΓRes_naturality, Category.assoc]
      exact congrArg (fun z ↦ F.ΓRes _ ≫ z)
        ((Scheme.pointSmallEtale (s x)).toPresheafFiber_naturality φ.hom
          (Scheme.Etale.mk (𝟙 C)) (Over.homMk (s x) (Category.comp_id _))).symm)
  have : G.Additive := Functor.additive_of_preserves_binary_products G
  have : G.PreservesEpimorphisms := ⟨by
    intro F F' φ hφ
    rw [← NatIso.naturality_2 e φ]
    have := epi_piObj_map T φ
    infer_instance⟩
  have : G.PreservesHomology := Functor.preservesHomology_of_preservesEpis_and_kernels G
  exact Functor.preservesFiniteColimits_of_preservesHomology G

end AlgebraicGeometry
