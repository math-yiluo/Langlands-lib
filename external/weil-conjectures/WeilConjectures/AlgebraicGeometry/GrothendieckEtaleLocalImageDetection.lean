/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GrothendieckEtaleLocalImage
import WeilConjectures.CategoryTheory.GrothendieckDirectedPullback

/-! # Detecting zero maps on the categorical local image
Source: Stacks Project, Tag 00WL, categorical image argument.
-/

@[expose] public section

universe u' u
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.FiniteSplitEtaleHypercover.Grothendieck

variable {X : Scheme.{u}} (A : Type u') [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A]

/-- Locally liftable maps detect zero on the local-image subobject, without any
assumption that the sheaf morphism is epic.
Source: Stacks Project, Tag 00WL, categorical image argument.
Proof: express the local image as the small directed union of its defining subobjects.
Pull this union back along x; AB5 says the resulting subobjects have union the source.
For each member pull its witnessing epimorphism back to this source subobject.
Its composite into B has the required local lifts, so the hypothesis kills it.
Cancel that epimorphism. All subobjects in the directed union now factor through
the kernel of g, hence the whole source does and g is zero.
(auxiliary; not a blueprint node). -/
theorem eq_zero_of_factors_localImage
    {F G : Sheaf X.smallEtaleTopology A} (p : F ⟶ G)
    (W : X.Etale) (B T : A) (x : B ⟶ G.obj.obj (op W)) (g : B ⟶ T)
    (hx : (localImage p W).Factors x)
    (hkill : ∀ (B' : A) (π : B' ⟶ B) (R : Sieve W), R ∈ X.smallEtaleTopology W →
      (∀ (Z : X.Etale) (f : Z ⟶ W), R f →
        ∃ l : B' ⟶ F.obj.obj (op Z), l ≫ p.hom.app (op Z) = π ≫ x ≫ G.obj.map f.op) →
      π ≫ g = 0) : g = 0 := by
  let S := localImageFamily p W
  have hsup : (⨆ i, (Subobject.pullback x).obj (S i)) = ⊤ :=
    IsGrothendieckAbelian.iSup_pullback_eq_top_of_factors x S
      (localImageFamily_directed p W) ((iSup_localImageFamily p W).symm ▸ hx)
  have hzero (i : LocalImageIndex p W) : ((Subobject.pullback x).obj (S i)).arrow ≫ g = 0 := by
    obtain ⟨P, e, he, R, hR, hl⟩ := localImageFamily_mem p W i
    have := he
    let U := (Subobject.pullback x).obj (S i)
    let a := Subobject.pullbackπ x (S i)
    have htest := hkill (pullback a e) (pullback.fst a e ≫ U.arrow) R hR (by
      intro Z f hf
      obtain ⟨l, hl⟩ := hl Z f hf
      refine ⟨pullback.snd a e ≫ l, ?_⟩
      rw [Category.assoc, hl]
      simp only [Category.assoc]
      rw [← pullback.condition_assoc]
      rw [(Subobject.isPullback x (S i)).w_assoc])
    apply (cancel_epi (pullback.fst a e)).1
    simpa [Category.assoc] using htest
  have hle : (⨆ i, (Subobject.pullback x).obj (S i)) ≤ kernelSubobject g :=
    iSup_le fun i ↦ Subobject.le_of_factors
      (kernelSubobject_factors g _ (hzero i))
  have hk : kernelSubobject g = ⊤ := top_le_iff.mp (hsup ▸ hle)
  have : Epi (kernelSubobject g).arrow := by rw [hk]; infer_instance
  apply (cancel_epi (kernelSubobject g).arrow).1
  simp

end AlgebraicGeometry.FiniteSplitEtaleHypercover.Grothendieck
