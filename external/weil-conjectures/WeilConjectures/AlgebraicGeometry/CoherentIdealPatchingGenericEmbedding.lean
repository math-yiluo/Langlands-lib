/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.IdealModuleProductStalk
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Preadditive.Biproducts
import WeilConjectures.AlgebraicGeometry.CoherentIdealPatchingGenericEmbeddingCore
import WeilConjectures.AlgebraicGeometry.CoherentIdealPatchingGenericEmbeddingStalkBijective
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# A generic embedding of an ideal multiple into an ideal sum

Source: Stacks Project, Cohomology of Schemes, Lemma 01YL, third proof paragraph
and final ideal intersection argument.
(blueprint: lem-weil-pbc-coherent-ideal-patching-generic-embedding).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits ZeroObject AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

/-- The geometric preparation for ideal patching, independent of any property of modules.
The positive sum of an ideal pushforward is either zero, or contains an ideal multiple
of the given coherent module, with a bijective generic stalk map.

Source: Stacks Project, Cohomology of Schemes, Lemma 01YL
(`coherent.tex`, `lemma-property-irreducible-higher-rank-cohomological`), third proof
paragraph and the final ideal intersection argument.
(blueprint: lem-weil-pbc-coherent-ideal-patching-generic-embedding).

Proof: The source of a finite closed immersion into a Noetherian scheme is Noetherian.
Every quasi-coherent ideal on it is coherent, and its finite pushforward is coherent.
Finite sums preserve coherence and vanish outside the closed image. For the zero ideal
choose rank one; its pushforward sum is zero.
For a nonzero ideal I, identify the image of the generic point of Z with ξ using sobriety
and the equality of closures. Apply the generic-point ideal inclusion to G to get a
nonzero ideal A and a mono β from a finite sum of its pushforward into G, bijective near ξ.
The generic stalk of G is nonzero because its support is the closed image, so the rank r
is positive. Put B = I ∩ A. On an integral scheme B is nonzero: on a nonempty affine open,
the product of nonzero local ideal sections is nonzero and lies in their intersection.
The two inclusions of B into A and I are bijective at the generic stalk. Thus the sum K
of its pushforward embeds both into G and into the sum M of the pushforward of I;
both maps are generically bijective. The coherent cokernel Q of K → G has zero ξ-stalk.
Its annihilator J is a quasi-coherent ideal and has unit ξ-stalk: Q vanishes on a
neighborhood of ξ since its support is closed. As J kills Q, multiplication JG → G
factors uniquely through K. Compose this factorization with K → M to obtain τ.
The product inclusion JG → G is mono, hence the factorization and τ are mono.
At ξ, J has unit stalk, so JG → G is bijective; both maps out of K are bijective too.
Consequently τ is bijective at ξ. This constructs only the geometric embedding;
it neither selects a subobject with an arbitrary property nor constructs its cokernel. -/
theorem coherent_ideal_patching_generic_embedding
    (X : Scheme.{u}) [IsLocallyNoetherian X] [CompactSpace X]
    (Z : Scheme.{u}) (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z]
    (ξ : X) (hclosure : closure ({ξ} : Set X) = Set.range i.base)
    (G : X.Modules) (hG : RingedSpace.IsCoherent X.toRingedSpace G)
    (hsupport : {x : X | ¬ Subsingleton (G.presheaf.stalk x)} = Set.range i.base)
    (hkill : ∀ g : X.presheaf.stalk ξ,
      ∀ m : (RingedSpace.moduleStalkFunctor X.toRingedSpace ξ).obj G,
        g ∈ IsLocalRing.maximalIdeal _ → g • m = 0)
    (I : Z.IdealSheafData) :
    ∃ (r : ℕ), 1 ≤ r ∧
      let M := @biproduct (Fin r) X.Modules _ _
        (fun _ : Fin r ↦ (pushforward i).obj I.toModules)
        (HasBiproduct.of_hasProduct (fun _ : Fin r ↦ (pushforward i).obj I.toModules))
      (IsZero M ∨
        ∃ (J : X.Modules) (ι : J ⟶ SheafOfModules.unit X.ringCatSheaf),
          Mono ι ∧ J.IsQuasicoherent ∧
          Function.Surjective
            ((RingedSpace.moduleStalkFunctor X.toRingedSpace ξ).map ι).hom ∧
          ∃ (τ : idealModuleProduct ι G ⟶ M), Mono τ ∧
            Function.Bijective
              ((RingedSpace.moduleStalkFunctor X.toRingedSpace ξ).map τ).hom) := by
  obtain ⟨r, hr, h⟩ :=
    coherent_ideal_patching_generic_embedding_core X Z i ξ hclosure G hG hsupport hkill I
  refine ⟨r, hr, ?_⟩
  let M := @biproduct (Fin r) X.Modules _ _
    (fun _ : Fin r ↦ (pushforward i).obj I.toModules)
    (HasBiproduct.of_hasProduct (fun _ : Fin r ↦ (pushforward i).obj I.toModules))
  change IsZero M ∨ _
  rcases h with hzero | ⟨J, ι, hιmono, hJqc, hιsurj, τ, hτmono, hτsurj⟩
  · exact Or.inl hzero
  · have hbij := coherent_ideal_patching_generic_embedding_stalk_bijective
      X Z i ξ hclosure G hG hsupport hkill I r M J ι τ hτmono hτsurj hιsurj
    exact Or.inr ⟨J, ι, hιmono, hJqc, hιsurj, τ, hτmono, hbij⟩

end AlgebraicGeometry.Scheme.Modules
