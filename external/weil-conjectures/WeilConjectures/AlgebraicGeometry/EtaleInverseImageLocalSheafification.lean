/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits
import Mathlib.CategoryTheory.Sites.LocallySurjective

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

/-- Source: Stacks Project, Étale Cohomology, Tag 09XN, proof of lemma-describe-pullback.
(blueprint: lem-weil-pbc-etale-inverse-image-section-description-core).

Proof:
Unfold Scheme.etaleSetPullback as sheafification of P. Local surjectivity of
its unit makes the sieve of arrows with P-representatives covering. The
small étale topology membership criterion extracts an étale cover with index
in Type u whose presieve lies in this sieve. Its objects and maps give Z and π;
its inclusion in the generated sieve proves covering, and image-sieve membership
supplies each representative and the required equality. -/
theorem etaleInverseImageSectionDescription_core (S T : Scheme.{u}) (g : T ⟶ S)
    (F : Sheaf S.smallEtaleTopology (Type (u + 1)))
    (s : ((Scheme.etaleSetPullback g).obj F).obj.obj (op (Scheme.Etale.mk (𝟙 T)))) :
    let P := (MorphismProperty.Over.pullback @Etale ⊤ g).op.lan.obj
      ((sheafToPresheaf S.smallEtaleTopology (Type (u + 1))).obj F)
    ∃ (I : Type u) (Z : I → T.Etale)
      (π : ∀ i : I, Z i ⟶ Scheme.Etale.mk (𝟙 T)),
      Sieve.ofArrows Z π ∈ T.smallEtaleTopology (Scheme.Etale.mk (𝟙 T)) ∧
      ∀ i : I, ∃ p : P.obj (op (Z i)),
        ((Scheme.etaleSetPullback g).obj F).obj.map (π i).op s =
          (toSheafify T.smallEtaleTopology P).app (op (Z i)) p := by
  classical
  let P := (MorphismProperty.Over.pullback @Etale ⊤ g).op.lan.obj
    ((sheafToPresheaf S.smallEtaleTopology (Type (u + 1))).obj F)
  have hs := Presheaf.imageSieve_mem T.smallEtaleTopology
    (toSheafify T.smallEtaleTopology P) s
  obtain ⟨𝒰, h𝒰, h, hle⟩ := (Scheme.mem_smallGrothendieckTopology _ _).mp hs
  let Z : 𝒰.I₀ → T.Etale := fun i ↦ (𝒰.X i).asOverProp T (h i)
  let π : ∀ i, Z i ⟶ Scheme.Etale.mk (𝟙 T) := fun i ↦ (𝒰.f i).asOverProp T
  refine ⟨𝒰.I₀, Z, π, ?_, ?_⟩
  · apply (Scheme.mem_smallGrothendieckTopology _ _).mpr
    exact ⟨𝒰, h𝒰, h, fun V f hf ↦ Sieve.le_generate _ _ _ hf⟩
  · intro i
    obtain ⟨p, hp⟩ := hle _ (π i) ⟨i⟩
    exact ⟨p, hp.symm⟩

end AlgebraicGeometry
