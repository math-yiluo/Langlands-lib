/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.ConstructibleSheaf.Defs
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.AlgebraicGeometry.FiniteFreeConstantLocalLift
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.RingTheory.Finiteness.Cardinality

/-!
# Local lifts of presentations of a finite constant quotient

Source: Stacks Project, Tag 093U, extension paragraph.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

/-- A finite constant quotient admits a module presentation whose constant sheaf map
lifts locally to the middle term of the extension.

Source: Stacks Project, Tag 093U, extension paragraph, through the choice of lifted generators.
(blueprint: lem-pc-constant-extension-presentation-lift)

Proof: On a nonempty base, a constant model N of the quotient has a stalk isomorphic
to N. The finite-stalk assumption therefore makes N finitely generated. Choose a finite
free surjection P → N, and form its kernel K, giving the module short exact sequence T.
Since the ring and the set of free generators are finite, P and its subset K are finite
sets. The finite set of all elements of K generates it, so K is finitely generated.
The generators of P map to sections of the quotient. Local surjectivity of the sheaf
epimorphism lifts each section on an etale cover; a finite common refinement lifts them
simultaneously. By the universal property of the constant free sheaf these lifts define r.
Its composite with the quotient map equals the constant presentation map, since the two
maps agree on the free generators. Constant sheaves commute with etale restriction,
which supplies e and the displayed identity. For an empty base use the empty cover. -/
theorem exists_constantExtension_presentation_lift {X : Scheme.{u}}
    {Λ : Type (u + 1)} [Ring Λ] [Finite Λ]
    {S : ShortComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hS : S.ShortExact) [S.X₃.IsConstant X.smallEtaleTopology]
    [IsFiniteSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) S.X₃] :
    ∃ 𝒰 : Cover.{u} etalePrecoverage X, ∀ i,
      ∃ T : ShortComplex (ModuleCat.{u + 1} Λ), T.ShortExact ∧ Module.Finite Λ T.X₁ ∧
        ∃ e : (constantSheaf (𝒰.X i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj T.X₃ ≅
          (Etale.upperStar (ModuleCat.{u + 1} Λ) (𝒰.f i)).obj S.X₃,
        ∃ r : (constantSheaf (𝒰.X i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj T.X₂ ⟶
          (Etale.upperStar (ModuleCat.{u + 1} Λ) (𝒰.f i)).obj S.X₂,
          r ≫ (Etale.upperStar (ModuleCat.{u + 1} Λ) (𝒰.f i)).map S.g =
            (constantSheaf (𝒰.X i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).map T.g ≫
              e.hom := by
  classical
  by_cases hX : Nonempty X
  · let x : X := hX.some
    let s : Spec (.of (SeparableClosure (X.residueField x))) ⟶ X :=
      (SpecToEquivOfField (SeparableClosure (X.residueField x)) _).2
        ⟨x, CommRingCat.ofHom (algebraMap (X.residueField x) _)⟩
    obtain ⟨N, ⟨eN⟩⟩ := Sheaf.IsConstant.mem_essImage (F := S.X₃)
    have : PreservesFilteredColimitsOfSize.{u, u}
        (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
      preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
    have : Module.Finite Λ N := by
      apply (ModuleCat.isFinitelyGenerated_iff N).mp
      exact (IsFiniteSheaf.isFinitelyGenerated_sheafFiber
        (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
        (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) (F := S.X₃)
        _ s).of_iso
          ((pointSmallEtale s).sheafFiber.mapIso eN.symm ≪≫
            (pointSmallEtale s).sheafFiberConstantSheafIso N)
    obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' Λ N
    let T := ShortComplex.moduleCatMk (LinearMap.ker p).subtype p
      (LinearMap.comp_ker_subtype p)
    have hT : T.ShortExact := by
      refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
      · apply (ShortComplex.moduleCat_exact_iff T).mpr
        intro v hv
        exact ⟨⟨v, hv⟩, rfl⟩
      · exact (ModuleCat.mono_iff_injective T.f).mpr Subtype.val_injective
      · exact (ModuleCat.epi_iff_surjective T.g).mpr hp
    have : Module.Finite Λ T.X₁ := by
      change Module.Finite Λ (LinearMap.ker p)
      exact Module.Finite.of_finite
    have : Epi S.g := hS.epi_g
    obtain ⟨𝒰, h𝒰⟩ := exists_finiteFreeConstant_local_lift S.g n
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map T.g ≫ eN.hom)
    refine ⟨𝒰, fun i ↦ ?_⟩
    obtain ⟨r, hr⟩ := h𝒰 i
    let P := Etale.upperStar (ModuleCat.{u + 1} Λ) (𝒰.f i)
    let c := upperStarConstantSheafIso (ModuleCat.{u + 1} Λ) (𝒰.f i)
    refine ⟨T, hT, inferInstance, c.symm.app N ≪≫ P.mapIso eN, r, ?_⟩
    rw [hr, Functor.map_comp]
    change c.inv.app T.X₂ ≫ P.map
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map T.g) ≫
        P.map eN.hom =
      (constantSheaf (𝒰.X i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).map T.g ≫
        c.inv.app N ≫ P.map eN.hom
    simpa only [P, T, ShortComplex.moduleCatMk, Functor.comp_map, Category.assoc]
      using congrArg (fun k ↦ k ≫ P.map eN.hom) (c.inv.naturality T.g).symm
  · have : IsEmpty X := not_nonempty_iff.mp hX
    let 𝒰 : Cover.{u} etalePrecoverage X :=
      Cover.mkOfCovers PEmpty (fun i ↦ PEmpty.elim i) (fun i ↦ PEmpty.elim i)
        (fun x ↦ isEmptyElim x) (fun i ↦ PEmpty.elim i)
    exact ⟨𝒰, fun i ↦ PEmpty.elim i⟩

end AlgebraicGeometry.Scheme
