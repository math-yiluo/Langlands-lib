/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import WeilConjectures.Algebra.Homology.SmoothPurity.PullbackExistsOfUniverses
import WeilConjectures.Algebra.Homology.SmoothPurity.PullbackPairingTransfer
import WeilConjectures.Algebra.Homology.SmoothPurity.PullbackDualFreeChart
import Mathlib.CategoryTheory.Sites.LocalProperties

/-!
# Pullback of the dual of a finite locally free module on a ringed site

Source: Stacks Project, Modules on Sites, Tags 0GMX and 0FNY; the Powers and duals
paragraph of `lemma-inverse-image-coefficient-sheaves--2`, main-20261015
(blueprint: lem-pur-ringed-site-finite-free-dual-pullback).

The coefficient morphism `a : R → u_* S` is the adjunct of the source's
`c : f⁻¹ R → S`. The module pullback is Mathlib's left adjoint, hence the same
sheafified relative tensor product. Its adjunction unit sends a section to its
pulled-back section. The equation below characterizes the canonical comparison
by evaluation on these sections, exactly as in Stacks 0GMX. In particular it
specializes to the stated Kronecker-delta formula for every local dual basis.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace SheafOfModules

set_option autoImplicit false

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {U : C ⥤ D} [U.IsContinuous J K]
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  {R : Sheaf J CommRingCat.{max u v w}} {S : Sheaf K CommRingCat.{max u v w}}
  (a : (sheafCompose J (forget₂ CommRingCat RingCat)).obj R ⟶
    (U.sheafPushforwardContinuous RingCat J K).obj
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S))

/-- Mathlib's module pullback with its existence proof supplied explicitly.
This transparent abbreviation permits the statement to assert existence of the
adjoint instead of imposing it as a further hypothesis. Source: Stacks Project,
Modules on Sites, Tags 03D7 and 0GMX
(blueprint: lem-pur-ringed-site-finite-free-dual-pullback). -/
noncomputable abbrev ringedSitePullbackFunctor
    (hAdj : (pushforward.{max u v w} a).IsRightAdjoint) :=
  @pullback _ _ _ _ _ _ _ _ _ _ a hAdj

/-- A section pulled back along a ringed site morphism, using the unit of the
module pullback adjunction. This is the image `1 ⊗ f⁻¹(m)` in the sheafified tensor
product. Source: Stacks Project, Modules on Sites, Tag 0GMX
(blueprint: lem-pur-ringed-site-finite-free-dual-pullback). -/
noncomputable def ringedSitePullbackSection
    (hAdj : (pushforward.{max u v w} a).IsRightAdjoint)
    (M : ringedSiteModules.{max u v w}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) (V : C)
    (m : M.val.obj (op V)) : ((ringedSitePullbackFunctor a hAdj).obj M).val.obj (op (U.obj V)) :=
  ((@pullbackPushforwardAdjunction _ _ _ _ _ _ _ _ _ _ a hAdj).unit.app M).val.app
    (op V) m

private theorem isIso_of_over_cover
    {E : Type u} [Category.{v} E] {H : GrothendieckTopology E}
    (A : Sheaf H RingCat.{max u v w})
    {I : Type (max u v w)} (X : I → E) (hX : H.CoversTop X)
    {M N : SheafOfModules.{max u v w} A} (f : M ⟶ N)
    (hf : ∀ i, IsIso (f.over (X i))) : IsIso f := by
  have : IsIso ((toSheaf A).map f) := by
    apply Sheaf.isIso_of_coversTop hX
    intro i
    have := hf i
    rw [← ObjectProperty.isIso_hom_iff, NatTrans.isIso_iff_isIso_app]
    intro T
    exact Functor.map_isIso (forget₂ _ AddCommGrpCat)
      (((evaluation (A.over (X i)) T).map (f.over (X i))))
  exact isIso_of_reflects_iso f (toSheaf A)

/-- The evaluation comparison is invertible for a finite locally free module,
contravariantly natural, and carries pulled-back dual bases to dual bases.
Source: Stacks Project, Modules on Sites, Tags 0GMX, 0FNY, 03EL and 04J0
(blueprint: lem-pur-ringed-site-finite-free-dual-pullback).

The comparison is specified, rather than taken as an arbitrary morphism: for
all local functionals `φ` and sections `m`, its evaluation on their pullbacks
is the coefficient image of `φ(m)`. The equation holds after every restriction,
since `V` is arbitrary. With `φ = eⱼ∨` and `m = eₖ` it says exactly that the
value is `δⱼₖ * 1`. The finite-free cover uses arbitrary ranks, including zero.

Proof: Construct the module left adjoint by
`module_pushforward_isRightAdjoint_of_universes`. Extend the evaluation pairing
by `exists_pullback_pairing_transfer`.
Its uniqueness gives uniqueness of the comparison family. For a morphism b,
the two naturality composites are extensions of the same pairing: adjunction
unit naturality makes both evaluate (φ,m) as the scalar image of φ(b(m)).
On each finite-free chart, `isIso_over_pullback_dual_of_free` makes the
restricted comparison invertible, using internal-Hom restriction and the
finite-biproduct calculation on the slice. Cover preservation and preservation of the
terminal object show that the objects U(V_i) cover D. Mathlib's
`Sheaf.isIso_of_coversTop` then detects invertibility of the underlying
additive sheaf map, and `toSheaf` reflects the resulting isomorphism. -/
theorem finite_free_dual_pullback
    [HasFiniteLimits C] [HasFiniteLimits D] [PreservesFiniteLimits U]
    (_hcover : CoverPreserving J K U)
    [∀ V : C, HasWeakSheafify (J.over V) AddCommGrpCat.{max u v w}]
    [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{max u v w}] :
    ∃ hAdj : (pushforward.{max u v w} a).IsRightAdjoint,
    ∃! δ : ∀ L : ringedSiteModules.{max u v w}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R),
        (ringedSitePullbackFunctor a hAdj).obj (homObj L (unit _)) ⟶
          homObj ((ringedSitePullbackFunctor a hAdj).obj L) (unit _),
      (∀ (L : ringedSiteModules.{max u v w}
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
          (V : C) (φ : (homObj L (unit _)).val.obj (op V)) (m : L.val.obj (op V)),
        (((δ L).val.app (op (U.obj V))
          (ringedSitePullbackSection a hAdj (homObj L (unit _)) V φ)).app
            (op (Over.mk (𝟙 (U.obj V)))))
          (ringedSitePullbackSection a hAdj L V m) =
            a.hom.app (op V) (φ.app (op (Over.mk (𝟙 V))) m)) ∧
      (∀ L M : ringedSiteModules.{max u v w}
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R),
        ∀ b : L ⟶ M,
          (ringedSitePullbackFunctor a hAdj).map (homObjMap b (𝟙 (unit _))) ≫ δ L =
            δ M ≫ homObjMap ((ringedSitePullbackFunctor a hAdj).map b) (𝟙 (unit _))) ∧
      (∀ L : ringedSiteModules.{max u v w}
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R),
        (∃ (I : Type (max u v w)) (V : I → C) (r : I → ℕ),
          Sieve.ofArrows V (fun i ↦ terminal.from (V i)) ∈ J (⊤_ C) ∧
            ∀ i : I, Nonempty (L.over (V i) ≅
              free (R := ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over (V i))
                (ULift.{max u v w} (Fin (r i))))) → IsIso (δ L)) := by
  classical
  have hAdj := module_pushforward_isRightAdjoint_of_universes a
  let := hAdj
  have transfer := exists_pullback_pairing_transfer a _hcover hAdj
  choose δ hδ hδunique using fun L ↦ transfer L (homObj L (unit _)) (𝟙 _)
  refine ⟨hAdj, δ, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro L V φ m
    exact hδ L V φ m
  · intro L M b
    obtain ⟨d, hd, unique⟩ := transfer L (homObj M (unit _)) (homObjMap b (𝟙 _))
    apply (unique _ ?_).trans (unique _ ?_).symm
    · intro V φ m
      have hnat := (pullbackPushforwardAdjunction a).unit.naturality
        (homObjMap b (𝟙 (unit _)))
      have heq : ringedSitePullbackSection a hAdj (homObj L (unit _)) V
          ((homObjMap b (𝟙 (unit _))).val.app (op V) φ) =
          (((pullback a).map (homObjMap b (𝟙 (unit _)))).val.app (op (U.obj V)))
            (ringedSitePullbackSection a hAdj (homObj M (unit _)) V φ) :=
        congrArg (fun f ↦ f.val.app (op V) φ) hnat
      exact (congrArg (fun ψ ↦ (((δ L).val.app (op (U.obj V)) ψ).app
        (op (Over.mk (𝟙 (U.obj V)))))
          (ringedSitePullbackSection a hAdj L V m)) heq).symm.trans
            (hδ L V ((homObjMap b (𝟙 (unit _))).val.app (op V) φ) m)
    · intro V φ m
      have hnat := (pullbackPushforwardAdjunction a).unit.naturality b
      have heq : ringedSitePullbackSection a hAdj M V (b.val.app (op V) m) =
          (((pullback a).map b).val.app (op (U.obj V)))
            (ringedSitePullbackSection a hAdj L V m) :=
        congrArg (fun f ↦ f.val.app (op V) m) hnat
      exact (congrArg (fun x ↦ (((δ M).val.app (op (U.obj V))
        (ringedSitePullbackSection a hAdj (homObj M (unit _)) V φ)).app
          (op (Over.mk (𝟙 (U.obj V))))) x) heq).symm.trans
            (hδ M V φ (b.val.app (op V) m))
  · intro L hL
    obtain ⟨I, V, r, hcover, he⟩ := hL
    have hcov : K.CoversTop (fun i ↦ U.obj (V i)) := by
      apply (K.coversTop_iff_of_isTerminal _
        ((terminalIsTerminal (C := C)).isTerminalObj U (⊤_ C))
        (fun i ↦ U.obj (V i))).2
      apply K.superset_covering _ (_hcover.cover_preserve hcover)
      rw [Sieve.functorPushforward_ofArrows]
      exact Sieve.ofArrows_le_ofObjects _ _
    apply isIso_of_over_cover _ _ hcov
    intro i
    exact isIso_over_pullback_dual_of_free a _hcover hAdj L (δ L) (hδ L)
      (V i) (r i) (he i)
  · intro ε hε
    funext L
    exact hδunique L (ε L) (hε.1 L)

end SheafOfModules
