/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import WeilConjectures.AlgebraicGeometry.ClosedImmersionCoherentEquivalence
import WeilConjectures.AlgebraicGeometry.ModuleSupportProperOverBase
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.ClosedImmersionFormalKernelAnnihilation
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # Transport of a formal comparison through a closed immersion

Source: Stacks Project, Theorem 088E, closed quotient and final comparison step.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
private theorem annihilated_of_system_iso {X : Scheme.{u}} [IsNoetherian X]
    (Q B : X.IdealSheafData) (M N : CoherentFormalModule X Q)
    (e : M.obj ≅ N.obj) (hN : AnnihilatedBy Q B N) : AnnihilatedBy Q B M := by
  intro n
  let : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
  obtain ⟨k, hk⟩ := formalModuleQuotient_factor B (e.hom.app (op n))
    (m := 1) (n := 1) (Nat.le_refl 1)
  have hz : Scheme.idealModuleProductι B.toModulesι (N.obj.obj (op n)) = 0 :=
    (hN n).eq_zero_of_src _
  have hi : Scheme.idealModuleProductι B.toModulesι (M.obj.obj (op n)) = 0 := by
    apply (cancel_mono (e.hom.app (op n))).1
    simpa only [Scheme.idealSheafPower, hz, comp_zero, zero_comp] using hk
  have : Mono (Scheme.idealModuleProductι B.toModulesι (M.obj.obj (op n))) := by
    dsimp [Scheme.idealModuleProductι]
    infer_instance
  apply IsZero.of_mono_eq_zero (Scheme.idealModuleProductι B.toModulesι _)
  exact hi

private theorem pushed_completion_supported {X Z T : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Z] [IsNoetherian T]
    (j : Z ⟶ X) [IsClosedImmersion j] (i : T ⟶ Z) [IsClosedImmersion i]
    (Q : X.IdealSheafData) (H : CoherentModules Z) (F : CoherentModules T)
    (e : H.obj ≅ (Scheme.Modules.pushforward i).obj F.obj)
    (N : CoherentFormalModule X Q)
    (d : N.obj ≅ ((completion Z (Q.comap j)).obj H).obj ⋙
      Scheme.Modules.pushforward j) :
    AnnihilatedBy Q (i ≫ j).ker N := by
  classical
  have hE := (closedImmersion_coherentFormal_equivalence (i ≫ j) Q).1
  rw [Scheme.IdealSheafData.comap_comp] at hE
  obtain ⟨E, ⟨η⟩⟩ := hE
  obtain ⟨θ, _⟩ := (closedImmersion_coherentFormal_equivalence i (Q.comap j)).2
  let D := (completion T ((Q.comap j).comap i)).obj F
  let C : CoherentFormalModule X Q := (E.functor.obj D).obj
  let h : N.obj ≅ C.obj := d ≪≫
    Functor.isoWhiskerRight ((formalCompletionFunctor (Q.comap j)).mapIso e)
      (Scheme.Modules.pushforward j) ≪≫
    Functor.isoWhiskerRight (θ.app F) (Scheme.Modules.pushforward j) ≪≫
    Functor.associator D.obj (Scheme.Modules.pushforward i) (Scheme.Modules.pushforward j) ≪≫
    Functor.isoWhiskerLeft D.obj (Scheme.Modules.pushforwardComp i j) ≪≫ (η.app D).symm
  exact annihilated_of_system_iso Q (i ≫ j).ker N C h (E.functor.obj D).property

private theorem ker_lt_map_power {X Z : Scheme.{u}} (j : Z ⟶ X)
    [IsClosedImmersion j] (L : Z.IdealSheafData)
    (hU : (L.support.compl : Set Z).Nonempty) (t : ℕ) (ht : 1 ≤ t) :
    j.ker < (L ^ t).map j := by
  have hle : j.ker ≤ (L ^ t).map j := by
    simpa using Scheme.IdealSheafData.map_mono j (bot_le : ⊥ ≤ L ^ t)
  refine lt_of_le_of_ne hle ?_
  intro heq
  obtain ⟨z, hz⟩ := hU
  have hzj := j.range_subset_ker_support (Set.mem_range_self z)
  rw [heq, Scheme.IdealSheafData.support_map] at hzj
  change j z ∈ closure (j '' (↑(L ^ t).support : Set Z)) at hzj
  rw [(j.isClosedEmbedding.isClosedMap _ (L ^ t).support.isClosed).closure_eq] at hzj
  obtain ⟨w, hw, hwz⟩ := hzj
  have hwz' : w = z := j.isClosedEmbedding.injective hwz
  subst w
  have hsupport : (L ^ t).support = L.support :=
    Scheme.IdealSheafData.support_pow L t (by omega)
  rw [hsupport] at hw
  exact hz hw

/-- Transport a comparison whose kernel is killed by a positive power of an ideal
with nonempty complementary open through a closed immersion. Proper support of the
coherent target makes the transported completion properly supported.

Source: Stacks Project, Theorem 088E, paragraphs 2--4, Tag 087T and Lemma 0CYS.
(blueprint: lem-weil-pbc-closed-immersion-formal-comparison-transport).

Proof: Termwise closed pushforward identifies coherent formal systems on Z with
systems killed by j.ker. Apply this to the completion of H and the given alpha,
and use the specified pushforward isomorphism to obtain a map from M to that
pushed completion N. Let B be L^t as a quasi-coherent ideal on Z and let J be its
inverse image under O_X -> j_*O_Z. On affine opens, J is the inverse image ideal
under the quotient ring map, so j.ker <= J. Choose a point of the nonempty open
complement of L.support. At its stalk L, and hence L^t, is the unit ideal; thus
B is not zero and the inverse image J strictly contains j.ker. The limiting fork
identifies k.pt with the kernel of alpha. Closed pushforward is exact, and systems
killed by j.ker are closed under kernels in the ambient formal category. The
universal property therefore identifies its pushforward with the kernel of the
transported map. On affine opens multiplication by J on a pushed module is
multiplication by its quotient ideal B, so the assumed annihilation kills this
kernel termwise. Finally use the scheme-theoretic support of coherent H. Proper
support makes its closed immersion proper over S, and its ideal kills H and all
quotients H/Q^n H. Compose this immersion with j: the resulting proper closed
subscheme in X kills all terms of N. This proves the conclusion for any chosen
Abelian structure, since kernel identifications use their universal properties. -/
theorem exists_closedImmersionFormalComparisonTransport
    {X Z S : Scheme.{u}} [IsNoetherian X] [IsNoetherian Z]
    (f : X ⟶ S) (j : Z ⟶ X) [IsClosedImmersion j]
    [LocallyOfFiniteType (j ≫ f)] (Q : X.IdealSheafData)
    [Abelian (CoherentFormalModule X Q)]
    (M : CoherentFormalModule X Q) (G : CoherentFormalModule Z (Q.comap j))
    (e : M.obj ≅ G.obj ⋙ Scheme.Modules.pushforward j)
    (H : CoherentModules Z)
    (hH : Scheme.Modules.HasSupportProperOver (j ≫ f) H.obj)
    (L : Z.IdealSheafData) (hU : (L.support.compl : Set Z).Nonempty)
    (α : G ⟶ (completion Z (Q.comap j)).obj H)
    (t : ℕ) (ht : 1 ≤ t) (k : KernelFork α) (hk : IsLimit k)
    (hkill : ∀ n : ℕ, IsZero (Scheme.idealModuleProduct
      (Scheme.idealSheafPower L.toModulesι t).2 (k.pt.obj.obj (op n)))) :
    ∃ (N : CoherentFormalModule X Q) (a : M ⟶ N) (J : X.IdealSheafData),
      j.ker < J ∧ AnnihilatedBy Q J (kernel a) ∧
      ∃ (T : Scheme.{u}) (i : T ⟶ X) (_ : IsClosedImmersion i),
        IsProper (i ≫ f) ∧ AnnihilatedBy Q i.ker N := by
  classical
  obtain ⟨E, ⟨η⟩⟩ := (closedImmersion_coherentFormal_equivalence j Q).1
  let D := (completion Z (Q.comap j)).obj H
  let N : CoherentFormalModule X Q := (E.functor.obj D).obj
  let d : N.obj ≅ D.obj ⋙ Scheme.Modules.pushforward j := η.app D
  let a : M ⟶ N := ObjectProperty.homMk
    (e.hom ≫ Functor.whiskerRight α.hom (Scheme.Modules.pushforward j) ≫ d.inv)
  have hsquare : a.hom ≫ d.hom =
      e.hom ≫ Functor.whiskerRight α.hom (Scheme.Modules.pushforward j) := by
    simp [a]
  have hker := closedImmersion_formalKernel_annihilated j Q M N G D a α e d
    hsquare L t k hk hkill
  have hcoh := (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType
    Z H.obj).mp H.property
  have : H.obj.IsQuasicoherent := hcoh.1
  have : H.obj.IsFiniteType := hcoh.2
  obtain ⟨T, i, hi, hp, _, F, hq, hf, ⟨he⟩⟩ :=
    (Scheme.Modules.module_support_proper_over_base (j ≫ f) H.obj).2.1.mp hH
  have : IsClosedImmersion i := hi
  have : IsNoetherian T := isNoetherian_of_locallyOfFiniteType i
  have : F.IsQuasicoherent := hq
  have : F.IsFiniteType := hf
  let FC : CoherentModules T := ⟨F,
    (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType T F).mpr ⟨hq, hf⟩⟩
  have hN := pushed_completion_supported j i Q H FC he N d
  refine ⟨N, a, (L ^ t).map j, ker_lt_map_power j L hU t ht, hker,
    T, i ≫ j, inferInstance, ?_, ?_⟩
  · simpa only [Category.assoc] using hp
  · exact hN

end AlgebraicGeometry
