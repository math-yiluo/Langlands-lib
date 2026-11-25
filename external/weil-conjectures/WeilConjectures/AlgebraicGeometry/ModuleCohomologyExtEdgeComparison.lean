/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Cohomology.FlatCohomologyComparison
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionEdge

/-! # Module/Ext comparisons compatible with the direct-image edge map

Source: Stacks Project, Tags 03FD, 01FB and 01F7.
(blueprint: new-module-cohomology-ext-edge-comparison)
-/

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules

/-- For the base-change projection f, comparisons can be chosen coherently
for the direct-image edge map.

Source: Stacks Project, Tag 03FD, Lemma 21.12.4; Tag 01FB, Remark 20.14.2;
Tag 01F7, Section 20.14.
(blueprint: new-module-cohomology-ext-edge-comparison)

Proof: Construct the comparisons on X and Y from forgotten injective module
resolutions. Their terms are acyclic for abelian sections (03FD), so taking
abelian sections computes the same cohomology as module sections. Identify Ext
from the free abelian sheaf on the terminal open with Ext from the constant
integer sheaf by evaluation at 1. Use this same identification on both schemes.
For a module map, an augmentation-preserving lift between resolutions computes
both maps, and homotopy independence gives naturality of each comparison.
For F on X, resolve F by I and resolve f_*I by an injective complex K on Y.
Resolve f_*F by J and lift its canonical augmentation into K. These choices
are exactly the 01FB diagram for the identity of f_*F. The section complexes
of I and f_*I agree by restriction along f inverse(Y)=X. The map into K is a
quasi-isomorphism on sections, hence its cohomology map is invertible.
Forgetting modules leaves the same diagram in abelian sheaves. Under the
constant-sheaf identification its map is inverse image on Ext followed by the
counit coefficient map coeff f (identity). Cancel the invertible vertical map
in the common diagram and transport through the two resolution comparisons.
This proves the edge equality; choices disappear by homotopy independence.
This statement uses only the identity coefficient map: a general coefficient
map must subsequently be handled by naturality on both cohomology models.
Degree zero, empty schemes and zero coefficients use the same section diagram.
No flatness or acyclicity of f_*F itself is assumed. -/
theorem exists_moduleCohomology_ext_edge_comparison
    {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
    {Y : Scheme.{u}} (h : Y ⟶ Spec (.of R)) (p : ℕ) :
    ∃ E : ∀ M : Y.Modules,
      ((RingedSpace.moduleCohomology Y.toRingedSpace p).obj M) ≃+ H M p,
    ∃ E' : ∀ M : (baseChangedScheme (S := B) h).Modules,
      ((RingedSpace.moduleCohomology
        (baseChangedScheme (S := B) h).toRingedSpace p).obj M) ≃+ H M p,
      (∀ (M M' : Y.Modules) (φ : M ⟶ M')
        (x : (RingedSpace.moduleCohomology Y.toRingedSpace p).obj M),
        E M' (((RingedSpace.moduleCohomology Y.toRingedSpace p).map φ).hom x) =
          H.map φ p (E M x)) ∧
      (∀ (M M' : (baseChangedScheme (S := B) h).Modules) (φ : M ⟶ M')
        (x : (RingedSpace.moduleCohomology
          (baseChangedScheme (S := B) h).toRingedSpace p).obj M),
        E' M' (((RingedSpace.moduleCohomology
          (baseChangedScheme (S := B) h).toRingedSpace p).map φ).hom x) =
          H.map φ p (E' M x)) ∧
      (∀ (F : (baseChangedScheme (S := B) h).Modules)
        (x : (RingedSpace.moduleCohomology Y.toRingedSpace p).obj
          ((pushforward (baseChangeFst (S := B) h)).obj F)),
        E' F (moduleCohomologyEdgeMap (baseChangeFst (S := B) h) F p x) =
          Sheaf.H.map (coeff (baseChangeFst (S := B) h)
            (𝟙 ((pushforward (baseChangeFst (S := B) h)).obj F))) p
            (Sheaf.H.mapFunctor (invImage (baseChangeFst (S := B) h))
              (constIso (baseChangeFst (S := B) h)).symm
              ((SheafOfModules.toSheaf Y.ringCatSheaf).obj
                ((pushforward (baseChangeFst (S := B) h)).obj F)) p
              (E ((pushforward (baseChangeFst (S := B) h)).obj F) x))) := by
  refine ⟨fun M ↦ moduleCohomologyExtResolutionEquiv Y M p,
    fun M ↦ moduleCohomologyExtResolutionEquiv (baseChangedScheme (S := B) h) M p,
    ?_, ?_, ?_⟩
  · exact moduleCohomologyExtResolutionEquiv_naturality Y p
  · exact moduleCohomologyExtResolutionEquiv_naturality (baseChangedScheme (S := B) h) p
  · intro F x
    exact moduleCohomologyExtResolutionEquiv_edge (baseChangeFst (S := B) h) F p x

end AlgebraicGeometry.Scheme.Modules
