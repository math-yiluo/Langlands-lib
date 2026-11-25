/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleResolutionSectionCanonicalComparison
public import WeilConjectures.AlgebraicGeometry.EtaleResolutionSectionCanonicalData
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
import WeilConjectures.AlgebraicGeometry.EtaleMayerVietorisInjectiveSectionsExact
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives

/-! # A boundary constructed from a fixed normalized resolution comparison

Source: Stacks Project, Tag 0A50, resolution proof.
(blueprint: def-weil-pbc-etale-mayer-vietoris-canonical-boundary).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

/-- Sections of a fixed injective resolution give a short exact complex sequence.
Source: Stacks Project, Tag 0A50, proof.
(blueprint: def-weil-pbc-etale-mayer-vietoris-canonical-boundary)

Proof: Every term of an injective resolution is injective. Apply degreewise
short exactness of sections of the covering opens, then the degreewise criterion
for short exactness of complexes. -/
theorem etaleSectionShortComplex_resolution_shortExact {X : Scheme.{u}}
    (U V : X.Opens) (hcover : U ⊔ V = ⊤)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (I : InjectiveResolution F) :
    (etaleSectionShortComplex U V I.cocomplex).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro q
  exact etaleSectionShortComplex_degreewise_shortExact U V hcover I.cocomplex q

/-- Transport the actual homology boundary through prescribed normalized comparisons.
Source: Stacks Project, Tag 0A50, resolution proof.
(blueprint: def-weil-pbc-etale-mayer-vietoris-canonical-boundary)

This construction chooses no existential boundary or comparison. The resolution
and its normalized comparisons are inputs, and the boundary is the homology
connecting map of their section short complex, conjugated by these comparisons. -/
noncomputable def etaleMayerVietorisCanonicalBoundary {X : Scheme.{u}}
    (U V : X.Opens) (hcover : U ⊔ V = ⊤)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (I : InjectiveResolution F)
    (c : ResolutionSectionCanonicalComparison F I) (q : ℕ) :
    Sheaf.H ((upperStar AddCommGrpCat.{u + 1} (U ⊓ V).ι).obj F) q →+
      Sheaf.H F (q + 1) :=
  (c.globalEquiv (q + 1)).toAddMonoidHom.comp
    (((etaleSectionShortComplex_resolution_shortExact U V hcover F I).δ
      q (q + 1) rfl).hom.comp (c.openEquiv (U ⊓ V) q).symm.toAddMonoidHom)

/-- The section short complex with its intersection named explicitly.
Source: Stacks Project, Tag 0A50, restriction pair and difference of restrictions.
(blueprint: def-weil-pbc-etale-mayer-vietoris-canonical-boundary)

The terms are constructed directly on U, V and W; equality transport of a
cohomology group is not used. The intersection equality supplies the inclusion proofs. -/
noncomputable def etaleSectionShortComplexOn {X : Scheme.{u}}
    (U V W : X.Opens) (hW : W = U ⊓ V)
    (I : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ) :
    ShortComplex (CochainComplex AddCommGrpCat.{u + 1} ℕ) := by
  let hU : W ≤ U := hW.le.trans inf_le_left
  let hV : W ≤ V := hW.le.trans inf_le_right
  let a : Scheme.Etale.mk U.ι ⟶ Scheme.Etale.mk (𝟙 X) :=
    MorphismProperty.Over.homMk U.ι (Category.comp_id _)
  let b : Scheme.Etale.mk V.ι ⟶ Scheme.Etale.mk (𝟙 X) :=
    MorphismProperty.Over.homMk V.ι (Category.comp_id _)
  let c : Scheme.Etale.mk W.ι ⟶ Scheme.Etale.mk U.ι :=
    MorphismProperty.Over.homMk (X.homOfLE hU) (X.homOfLE_ι _)
  let d : Scheme.Etale.mk W.ι ⟶ Scheme.Etale.mk V.ι :=
    MorphismProperty.Over.homMk (X.homOfLE hV) (X.homOfLE_ι _)
  refine ShortComplex.mk
    (biprod.lift (etaleSectionMap a I) (etaleSectionMap b I))
    (biprod.desc (etaleSectionMap c I) (-etaleSectionMap d I)) ?_
  simp only [biprod.lift_desc, Preadditive.comp_neg, ← sub_eq_add_neg, sub_eq_zero]
  apply HomologicalComplex.hom_ext
  intro n
  change (I.X n).obj.map a.op ≫ (I.X n).obj.map c.op =
    (I.X n).obj.map b.op ≫ (I.X n).obj.map d.op
  rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp]
  congr 2
  apply MorphismProperty.Over.Hom.ext
  exact (X.homOfLE_ι hU).trans (X.homOfLE_ι hV).symm

/-- Exactness of the directly constructed section complex with named intersection.
Source: Stacks Project, Tag 0A50, the degreewise injective-section criterion.
(blueprint: def-weil-pbc-etale-mayer-vietoris-canonical-boundary)

Proof: Substitute W=U intersection V. The directly constructed short complex
is the standard section short complex; its two inclusion proofs agree by proof
irrelevance. Apply resolution section short exactness. -/
theorem etaleSectionShortComplexOn_shortExact {X : Scheme.{u}}
    (U V W : X.Opens) (hW : W = U ⊓ V) (hcover : U ⊔ V = ⊤)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (I : InjectiveResolution F) :
    (etaleSectionShortComplexOn U V W hW I.cocomplex).ShortExact := by
  subst W
  exact etaleSectionShortComplex_resolution_shortExact U V hcover F I

/-- The boundary with a specified intersection open, constructed without data transport.
Source: Stacks Project, Tag 0A50, section-complex boundary construction.
(blueprint: def-weil-pbc-etale-mayer-vietoris-canonical-boundary)

Use the section complex constructed directly on W and the normalized comparison
c.openEquiv W. Its boundary has the prescribed domain from the outset. Only the
proofs of inclusions and short exactness use the intersection equality. -/
noncomputable def etaleMayerVietorisBoundaryOn {X : Scheme.{u}}
    (U V W : X.Opens) (hW : W = U ⊓ V) (hcover : U ⊔ V = ⊤)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (I : InjectiveResolution F)
    (c : ResolutionSectionCanonicalComparison F I) (q : ℕ) :
    Sheaf.H ((upperStar AddCommGrpCat.{u + 1} W.ι).obj F) q →+ Sheaf.H F (q + 1) :=
  (c.globalEquiv (q + 1)).toAddMonoidHom.comp
    (((etaleSectionShortComplexOn_shortExact U V W hW hcover F I).δ
      q (q + 1) rfl).hom.comp (c.openEquiv W q).symm.toAddMonoidHom)

/-- The fixed injective resolution behind the boundary API.
Source: Stacks Project, Tag 0A50, injective-resolution construction.
(blueprint: def-weil-pbc-etale-mayer-vietoris-canonical-boundary)

This is the library's chosen injective resolution, exposed through a small typed
constant so that boundary uses do not elaborate its instance construction again. -/
@[irreducible] noncomputable def etaleMayerVietorisFixedResolution {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) : InjectiveResolution F :=
  injectiveResolution F

/-- The fixed comparison is determined by its values on all representing cocycles.
Source: Stacks Project, Tags 0A50 and 03F3, normalized resolution comparison.
(blueprint: def-weil-pbc-etale-mayer-vietoris-canonical-boundary)

The normalization determines the equivalences on every homology class. This
choice therefore fixes no unspecified data; it is the prescribed normalized comparison. -/
@[irreducible] noncomputable def etaleMayerVietorisFixedComparison {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    ResolutionSectionCanonicalComparison F (etaleMayerVietorisFixedResolution F) :=
  Classical.choice (exists_resolutionSection_canonical_comparison F
    (etaleMayerVietorisFixedResolution F))

/-- Boundary with canonical resolution choices hidden behind a small typed interface.
Source: Stacks Project, Tag 0A50, injective-resolution construction.
(blueprint: def-weil-pbc-etale-mayer-vietoris-canonical-boundary)

The resolution is the chosen injective resolution. The normalized comparison is
uniquely determined on cocycles, so choosing it does not choose unspecified data.
The boundary is the explicit section-complex homology boundary above. -/
@[irreducible] noncomputable def etaleMayerVietorisFixedBoundary {X : Scheme.{u}}
    (U V W : X.Opens) (hW : W = U ⊓ V) (hcover : U ⊔ V = ⊤)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :
    Sheaf.H ((upperStar AddCommGrpCat.{u + 1} W.ι).obj F) q →+ Sheaf.H F (q + 1) :=
  etaleMayerVietorisBoundaryOn U V W hW hcover F
    (etaleMayerVietorisFixedResolution F) (etaleMayerVietorisFixedComparison F) q

end AlgebraicGeometry.Etale
