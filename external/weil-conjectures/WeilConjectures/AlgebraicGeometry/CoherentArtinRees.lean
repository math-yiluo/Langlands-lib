/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
import WeilConjectures.AlgebraicGeometry.ArtinReesAffineComparison
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.CoherentAffineSectionsFinite
import Mathlib.RingTheory.Filtration
import WeilConjectures.AlgebraicGeometry.Modules.FreeGenerator

/-! # Artin-Rees for coherent modules on a Noetherian scheme

Source: Stacks Project, Cohomology of Schemes, Lemma 01YA (lemma-Artin-Rees)
(blueprint: lem-weil-pbc-coherent-artin-rees).

The pullback of the two inclusions represents their sectionwise intersection. Equalities
and inclusions of subsheaves are expressed by their images in the sections of `F` on every
open. Powers and multiplication images use the shared definitions from the formal-module
node, including the zeroth power of the ideal.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme


private theorem app_injective {X : Scheme.{u}} {M N : X.Modules}
    (j : M ⟶ N) [Mono j] (W : X.Opens) : Function.Injective (j.app W) := by
  have : Mono (j.val.app (.op W)) :=
    (SheafOfModules.evaluation X.ringCatSheaf (.op W)).map_mono j
  exact (ModuleCat.mono_iff_injective _).mp inferInstance

private theorem range_of_locally_range {X : Scheme.{u}} {M N : X.Modules}
    (j : M ⟶ N) [Mono j] {ι : Type*} (V : ι → X.Opens) (W : X.Opens)
    (hVW : ∀ i, V i ≤ W) (hcover : W ≤ ⨆ i, V i) (s : Γ(N, W))
    (hs : ∀ i, N.presheaf.map (homOfLE (hVW i)).op s ∈ Set.range (j.app (V i))) :
    s ∈ Set.range (j.app W) := by
  classical
  choose t ht using hs
  have hcompat : TopCat.Presheaf.IsCompatible M.presheaf V t := by
    intro i k
    apply app_injective j (V i ⊓ V k)
    rw [Modules.Hom.app_presheaf_map, Modules.Hom.app_presheaf_map, ht i, ht k]
    change N.presheaf.map (homOfLE inf_le_left).op
        (N.presheaf.map (homOfLE (hVW i)).op s) =
      N.presheaf.map (homOfLE inf_le_right).op
        (N.presheaf.map (homOfLE (hVW k)).op s)
    simp only [Modules.presheaf_map_homOfLE_map_homOfLE]
  obtain ⟨z, hz, _⟩ := TopCat.Sheaf.existsUnique_gluing' ⟨M.presheaf, M.isSheaf⟩
    V W (fun i ↦ homOfLE (hVW i)) hcover t hcompat
  refine ⟨z, ?_⟩
  apply TopCat.Sheaf.eq_of_locally_eq' ⟨N.presheaf, N.isSheaf⟩
    V W (fun i ↦ homOfLE (hVW i)) hcover
  intro i
  rw [← Modules.Hom.app_presheaf_map, hz i, ht i]

/-- Artin-Rees for a quasi-coherent subsheaf `g : G ⟶ F` of a coherent module `F`.
The constant `c` is uniform over all opens and all `n ≥ c`. The first clause is the equality
I^(n-c)(I^c F ∩ G) = I^n F ∩ G; the second is its inclusion in I^(n-c) G, all inside F.

Source: Stacks Project, Cohomology of Schemes, Lemma 01YA (lemma-Artin-Rees)
(blueprint: lem-weil-pbc-coherent-artin-rees).

Proof:
1. Coherence gives quasi-coherence and finite type. Apply the existing coherent
   affine-sections theorem to obtain finite sections on each affine open.
2. Apply Mathlib's module Artin-Rees lemma to the image of g on each affine open.
   Choose a finite affine subcover by quasi-compactness and take the maximum c of
   its bounds, using zero for an empty cover. The formulas at c and n, together
   with (n-c)+(c-k)=n-k and multiplication of ideal powers, show that c works
   in the section modules of every member of this cover.
3. Apply artin_rees_affine_comparison on each covering affine to obtain equality
   on its subopens. For any W intersect the cover with W. Membership in the range
   of a monomorphism is local: its local preimages agree by injectivity on overlaps
   and glue by the sheaf axiom. Apply this to both inclusions and to their product
   intersection inclusion to descend the equality to W.
4. Use formalModuleQuotient_factor on the pullback's projection to G with equal
   exponents n-c. The pullback identity shows that the left side factors through
   I^(n-c) G → F. The equality from step 3 gives the asserted inclusion. -/
theorem coherent_artin_rees {X : Scheme.{u}} [IsNoetherian X]
    (F G : X.Modules) (hF : RingedSpace.IsCoherent X.toRingedSpace F)
    (g : G ⟶ F) [Mono g] (hG : G.IsQuasicoherent) (I : X.IdealSheafData) :
    ∃ c : ℕ, ∀ n : ℕ, c ≤ n → ∀ W : X.Opens,
      Set.range ((idealModuleProductι (idealSheafPower I.toModulesι (n - c)).2
        (pullback (idealModuleProductι (idealSheafPower I.toModulesι c).2 F) g) ≫
          pullback.fst (idealModuleProductι (idealSheafPower I.toModulesι c).2 F) g ≫
            idealModuleProductι (idealSheafPower I.toModulesι c).2 F).app W) =
        Set.range ((idealModuleProductι (idealSheafPower I.toModulesι n).2 F).app W) ∩
          Set.range (g.app W) ∧
      Set.range ((idealModuleProductι (idealSheafPower I.toModulesι n).2 F).app W) ∩
          Set.range (g.app W) ⊆
        Set.range ((idealModuleProductι (idealSheafPower I.toModulesι (n - c)).2 G ≫
          g).app W) := by
  classical
  have hqc := (Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType X F).mp hF
  have : F.IsQuasicoherent := hqc.1
  have : F.IsFiniteType := hqc.2
  have : G.IsQuasicoherent := hG
  have hfinite (U : X.affineOpens) : Module.Finite Γ(X, U.1) Γ(F, U.1) :=
    Modules.coherent_affine_sections_finite X F hF U.1 U.2
  have hlocal (U : X.affineOpens) : ∃ k : ℕ, ∀ n : ℕ, k ≤ n →
      I.ideal U ^ n • (⊤ : Submodule Γ(X, U.1) Γ(F, U.1)) ⊓
        LinearMap.range (g.val.app (.op U.1)).hom =
      I.ideal U ^ (n - k) • (I.ideal U ^ k •
        (⊤ : Submodule Γ(X, U.1) Γ(F, U.1)) ⊓
          LinearMap.range (g.val.app (.op U.1)).hom) := by
    have := hfinite U
    have := IsLocallyNoetherian.component_noetherian U
    exact Ideal.exists_pow_inf_eq_pow_smul (I.ideal U) _
  choose k hk using hlocal
  have hcover : (Set.univ : Set X) ⊆ ⋃ U : X.affineOpens, (U.1 : Set X) := by
    intro x _
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, _⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact Set.mem_iUnion.mpr ⟨⟨U, hU⟩, hxU⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun U : X.affineOpens ↦ (U.1 : Set X)) (fun U ↦ U.1.2) hcover
  let c := s.sup k
  refine ⟨c, ?_⟩
  intro n hn W
  let a := idealModuleProductι (idealSheafPower I.toModulesι c).2 F
  let b := idealModuleProductι (idealSheafPower I.toModulesι n).2 F
  let l := idealModuleProductι (idealSheafPower I.toModulesι (n - c)).2
    (pullback a g) ≫ pullback.fst a g ≫ a
  have ha : Mono a := by dsimp [a, idealModuleProductι]; infer_instance
  have hb : Mono b := by dsimp [b, idealModuleProductι]; infer_instance
  have hl : Mono l := by
    have : Mono (idealModuleProductι (idealSheafPower I.toModulesι (n - c)).2
        (pullback a g)) := by dsimp [idealModuleProductι]; infer_instance
    dsimp only [l]
    infer_instance
  let V : s → X.Opens := fun i ↦ W ⊓ i.1.1
  have hVW : ∀ i, V i ≤ W := fun _ ↦ inf_le_left
  have hVcover : W ≤ ⨆ i, V i := by
    intro x hx
    obtain ⟨U, hxU⟩ := Set.mem_iUnion.mp (hs (Set.mem_univ x))
    obtain ⟨hUs, hxU⟩ := Set.mem_iUnion.mp hxU
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨U, hUs⟩, hx, hxU⟩
  have heq (i : s) : Set.range (l.app (V i)) =
      Set.range (b.app (V i)) ∩ Set.range (g.app (V i)) := by
    apply artin_rees_affine_comparison F G g I i.1 c n _ (V i) inf_le_right
    have hc : k i.1 ≤ c := Finset.le_sup i.2
    rw [hk i.1 n (hc.trans hn), hk i.1 c hc, ← Submodule.mul_smul, ← pow_add]
    congr 2
    omega
  have hrestrict {M : X.Modules} (f : M ⟶ F) (t : Γ(F, W))
      (ht : t ∈ Set.range (f.app W)) (i : s) :
      F.presheaf.map (homOfLE (hVW i)).op t ∈ Set.range (f.app (V i)) := by
    obtain ⟨z, rfl⟩ := ht
    exact ⟨M.presheaf.map (homOfLE (hVW i)).op z,
      Modules.Hom.app_presheaf_map f (homOfLE (hVW i)) z⟩
  have hglobal : Set.range (l.app W) =
      Set.range (b.app W) ∩ Set.range (g.app W) := by
    ext t
    constructor
    · intro ht
      exact ⟨range_of_locally_range b V W hVW hVcover t
        (fun i ↦ (heq i ▸ hrestrict l t ht i).1),
        range_of_locally_range g V W hVW hVcover t
        (fun i ↦ (heq i ▸ hrestrict l t ht i).2)⟩
    · intro ht
      apply range_of_locally_range l V W hVW hVcover t
      intro i
      rw [heq i]
      exact ⟨hrestrict b t ht.1 i, hrestrict g t ht.2 i⟩
  refine ⟨hglobal, ?_⟩
  intro t ht
  obtain ⟨z, hz⟩ := hglobal.symm ▸ ht
  obtain ⟨q, hq⟩ := formalModuleQuotient_factor I (pullback.snd a g)
    (m := n - c) (n := n - c) le_rfl
  refine ⟨q.app W z, ?_⟩
  have h : l = q ≫ idealModuleProductι (idealSheafPower I.toModulesι (n - c)).2 G ≫ g := by
    dsimp only [l]
    rw [pullback.condition, ← Category.assoc, hq, Category.assoc]
  exact (congrArg (fun f ↦ f.app W z) h).symm.trans hz

end AlgebraicGeometry.Scheme
