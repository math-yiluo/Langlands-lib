/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import WeilConjectures.AlgebraicGeometry.GrothendieckEtaleLocalImageSheaf
import WeilConjectures.AlgebraicGeometry.GrothendieckEtaleLocalImageDetection

/-! # Local lifting families for general Grothendieck coefficients

Source: the local epimorphism argument for sheaves, Stacks Project, Tags 00WL and 01H0.
The categorical formulation below is an explicit coefficient generalization.
-/

@[expose] public section

universe u' u
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.FiniteSplitEtaleHypercover.Grothendieck

variable {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
variable (A : Type u') [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A]

omit [CompactSpace X] [QuasiSeparatedSpace X] in
private lemma localImage_eq_top_of_isSheaf
    {F G : Sheaf X.smallEtaleTopology A} (p : F ⟶ G) [Epi p]
    (hs : Presheaf.IsSheaf X.smallEtaleTopology (qcqsLocalImagePresheaf p))
    (W : X.Etale) [CompactSpace W.left] [QuasiSeparatedSpace W.left] :
    localImage p W = ⊤ := by
  let L : Sheaf X.smallEtaleTopology A := ⟨qcqsLocalImagePresheaf p, hs⟩
  let i : L ⟶ G := ⟨qcqsLocalImageι p⟩
  let q : F ⟶ L := ⟨toQcqsLocalImage p⟩
  have hi : q ≫ i = p := by
    apply Sheaf.hom_ext
    exact toQcqsLocalImage_ι p
  have : Epi i := epi_of_epi_fac hi
  have (Z : X.Etaleᵒᵖ) : Mono (i.hom.app Z) :=
    inferInstanceAs (Mono (qcqsLocalImage p Z.unop).arrow)
  have : Mono i.hom := NatTrans.mono_of_mono_app _
  have : Mono ((sheafToPresheaf X.smallEtaleTopology A).map i) := ‹Mono i.hom›
  have : Mono i := (sheafToPresheaf X.smallEtaleTopology A).mono_of_mono_map inferInstance
  have : IsIso i := isIso_of_mono_of_epi i
  have : IsIso ((sheafToPresheaf X.smallEtaleTopology A).map i) := inferInstance
  have : IsIso i.hom := this
  have : IsIso ((qcqsLocalImage p W).arrow) :=
    inferInstanceAs (IsIso (i.hom.app (op W)))
  exact (qcqsLocalImage_eq p W).symm.trans (Subobject.eq_top_of_isIso_arrow _)

set_option linter.unusedSectionVars false in
/-- Maps admitting local lifts through a sheaf epimorphism jointly detect zero maps.
Source: Stacks Project, Sites, Tag 00WL, the image subsheaf argument, and
Hypercoverings, Tag 01H0, the local primitive step. This is the categorical
finite-cover version for Grothendieck abelian coefficients.
(auxiliary; not a blueprint node).

Proof: define the local image at each etale object as the union of subobjects whose
inclusions lift locally after an epimorphism onto their source. These subobjects form a
small directed family: use well-poweredness for smallness, and biproducts and intersection
of covering sieves for directedness. Restriction preserves the family. Extend from qcqs
objects by intersecting the pullbacks of their local-image subobjects over all qcqs tests.
This constructs a subpresheaf of G containing the image of p.

The union pulls back to the whole source of any map factoring through it, by AB5.
For each pulled-back member, pull back its witnessing epimorphism. The resulting map into
the source has local lifts. The vanishing hypothesis kills it; cancel the epimorphism.
All the pulled-back members therefore lie in the kernel of g, and their union is the
whole source. This proves the detection assertion for maps into the local image.

To show that the constructed subpresheaf is a sheaf, first prove finite-cover descent
for factoring through the local image. Compose a proposed map with the cokernel of the
local-image inclusion. When all its restrictions actually lift locally, transitivity of
covering sieves kills this composite. Remove those lifting assumptions one cover member
at a time using the detection assertion and finite induction. Thus factorization through
the local image descends along a finite cover. For an arbitrary compatible family, glue
it in G. Pull the covering sieve back to each qcqs test object, refine to a finite affine
cover, and apply finite-cover descent. The glued map factors through the constructed
subpresheaf. Monicity gives uniqueness, so it is a subsheaf.

The factorization of p through this subsheaf makes its inclusion epic. It is also monic,
hence an isomorphism in the abelian sheaf category. On qcqs W the extended local image
equals the original one, which is therefore top. Apply the detection assertion to x.
Neither a fixed projective source nor factorization through one stage of a directed union
is used. Empty finite covers, empty W, zero coefficients, and zero source are included. -/
theorem eq_zero_of_locally_liftable_maps
    {F G : Sheaf X.smallEtaleTopology A} (p : F ⟶ G) [Epi p]
    (W : X.Etale) [CompactSpace W.left] [QuasiSeparatedSpace W.left]
    (B T : A) (x : B ⟶ G.obj.obj (op W)) (g : B ⟶ T)
    (hkill : ∀ (B' : A) (π : B' ⟶ B) (R : Sieve W), R ∈ X.smallEtaleTopology W →
      (∀ (Z : X.Etale) (f : Z ⟶ W), R f →
        ∃ l : B' ⟶ F.obj.obj (op Z), l ≫ p.hom.app (op Z) = π ≫ x ≫ G.obj.map f.op) →
      π ≫ g = 0) : g = 0 := by
  have htop : localImage p W = ⊤ :=
    localImage_eq_top_of_isSheaf A p (qcqsLocalImage_isSheaf A p) W
  apply eq_zero_of_factors_localImage A p W B T x g
  · rw [htop]
    exact Subobject.top_factors x
  · exact hkill

end AlgebraicGeometry.FiniteSplitEtaleHypercover.Grothendieck
