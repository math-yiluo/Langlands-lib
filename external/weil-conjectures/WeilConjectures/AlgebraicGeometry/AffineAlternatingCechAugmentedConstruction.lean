/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffineAlternatingCechModel
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.AlgebraicGeometry.AlternatingCechSheafTerms
import WeilConjectures.AlgebraicGeometry.AlternatingCechSheafLocalContraction
import WeilConjectures.AlgebraicGeometry.AlternatingCechSheafAffineComparison

/-! # Augmented increasing-tuple complex of module sheaves

Source: Stacks Project, Tags 01FM, 02KG, 02KH (only its Cech comparison),
and the construction paragraph of
`lem-pc-s3-affine-alternating-cech-resolution-core`.
(blueprint: lem-pc-s3-affine-alternating-cech-augmented-construction).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry

/-- Construct the augmented increasing-tuple sheaf complex and its affine section model.
Source: Stacks Project, Tag 01FM (alternating complexes), Tag 02KG (affine base
change), and Tag 02KH, proof of the separated case (comparison of Cech complexes
before taking cohomology); parent resolution node, construction paragraph.
(blueprint: lem-pc-s3-affine-alternating-cech-augmented-construction).

Proof: In degree n take the finite product of j_* (G restricted to W), where W is
an intersection indexed by a strictly increasing (n+1)-tuple in Fin r. On sections
over V, each factor is G(V intersect W), with scalar action through restriction.
The face maps are restrictions, with alternating signs. Functoriality of restriction
and cancellation of the two orders of deleting two entries prove d squared zero.
Augment by restricting sections from G to each cover member. On U_i, insert i into
a tuple, sort with its permutation sign, and use zero when an index repeats. The
signed face sum gives dh+hd=identity on the augmented complex. Thus the augmentation
is locally a homotopy equivalence, hence a quasi-isomorphism. The same homotopy after
any additive tensor pullback contracts the pulled-back augmented complex on the
inverse-image cover; no flatness is used. Extending by zero preserves this assertion.
Each W is affine since f is separated over an affine base. Enumerate the finite
increasing-tuple type by Fin m; the empty type gives m=0. Pushforward preserves
products. On an affine intersection the tilde-Gamma counit identifies its direct
image on Spec A with tilde of its sections restricted to A. Naturality with respect
to restriction identifies every signed face map, so these finite-product comparisons
assemble into q. Negative degrees on both sides are zero. For an empty cover X is
empty and the zero complex and unique augmentation satisfy all assertions.
The complex is used only as an existential witness, never to define arbitrary data. -/
theorem exists_affineAlternatingCech_augmented_construction
    {A B : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec A)
    [IsSeparated f] (g : Spec B ⟶ Spec A)
    {r : ℕ} (U : Fin r → X.Opens) (hU : iSup U = ⊤)
    (haffine : ∀ i, IsAffineOpen (U i))
    [(Scheme.Modules.tensorPullback (pullback.fst f g)).Additive]
    (G : X.Modules) [SheafOfModules.IsQuasicoherent.{u} G] :
    ∃ (C : CochainComplex X.Modules ℕ)
      (ε : (CochainComplex.single₀ X.Modules).obj G ⟶ C),
      Nonempty (((Scheme.Modules.pushforward f).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (C.extend ComplexShape.embeddingUpNat) ≅
          affineAlternatingCechModel f U G) ∧
      QuasiIso ε ∧
      QuasiIso (((Scheme.Modules.tensorPullback (pullback.fst f g)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (HomologicalComplex.extendMap ε
          ComplexShape.embeddingUpNat)) ∧
      ∀ k : ℕ, ∃ (n : ℕ) (W : Fin n → X.Opens),
        (∀ j, IsAffineOpen (W j)) ∧
        Nonempty (C.X k ≅ ∏ᶜ fun j : Fin n ↦
          (Scheme.Modules.pushforward (W j).ι).obj (G.restrict (W j).ι)) := by
  classical
  have hsep : IsSeparated (terminal.from X) := by
    have h : IsSeparated (f ≫ terminal.from (Spec A)) := inferInstance
    simpa only [terminal.comp_from] using h
  let : X.IsSeparated := ⟨hsep⟩
  obtain ⟨hε, hpε⟩ := alternatingCechSheafAugmentation_quasiIso (pullback.fst f g) U hU G
  refine ⟨alternatingCechSheafComplex U G, alternatingCechSheafAugmentation U G,
    alternatingCechSheafComplex_affineComparison f U haffine G, hε, hpε, ?_⟩
  intro k
  let T := Fin (k + 1) ↪o Fin r
  let e : T ≃ Fin (Fintype.card T) := Fintype.equivFin T
  let W : Fin (Fintype.card T) → X.Opens := fun j ↦ alternatingCechIntersection U (e.symm j)
  obtain ⟨q⟩ := alternatingCechSheafComplex_terms U G k
  refine ⟨Fintype.card T, W, ?_, ?_⟩
  · intro j
    exact IsAffineOpen.iInf fun l ↦ haffine (e.symm j l)
  · exact ⟨q ≪≫ (Pi.reindex e.symm (fun t : T ↦
      (Scheme.Modules.pushforward (alternatingCechIntersection U t).ι).obj
        (G.restrict (alternatingCechIntersection U t).ι))).symm⟩

end AlgebraicGeometry
