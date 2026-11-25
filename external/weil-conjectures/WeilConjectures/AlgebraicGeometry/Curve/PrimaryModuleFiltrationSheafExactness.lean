/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.PrimaryModuleFiltrationFixedFieldComparison
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Quotient comparison for a single invariant subgroup inclusion

Source: Stacks Project, Tags 04JQ and 03QT; blueprint `theorem-cohomology-curves--2`,
proof paragraphs 1--2.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits ZeroObject Opposite
namespace AlgebraicGeometry.Scheme

/-- Source: Stacks Project, Tags 04JQ and 03QT; blueprint
`theorem-cohomology-curves--2`, proof paragraphs 1--2.
(blueprint: lem-sc-primary-subgroup-sheaf-exactness)

Proof: The inclusion of A into B is injective. Its quotient is B/A, explicitly the
quotient of B.toIntSubmodule by the comap of A.toIntSubmodule under the subtype map.
For g in H, the hypothesis g*x-x in A says the induced action on B/A is the identity.
Thus the projection to primaryTrivialQuotient is equivariant. Its kernel is precisely
A and it is surjective, giving a short exact sequence of discrete H-modules. All
stabilizers in A and B are restrictions of open ambient stabilizers; those in the
trivial quotient are the whole group. The equivalence C.inverse preserves the
kernel and cokernel universal properties and therefore exactness, monomorphisms and
epimorphisms. Pullback across the scheme isomorphism e is an equivalence of sheaf
categories and does the same. The cokernel of the resulting inclusion is consequently
isomorphic to the associated sheaf of this specific quotient. The complex in the
conclusion was constructed from precisely this inclusion and its cokernel projection.
This works when A=B or B=0: the quotient and its associated sheaf are zero. No finiteness,
prime, filtration, initial stage or terminal comparison is used. -/
theorem primarySheafSequence_shortExact
    (K Ks Ω : Type u) [Field K] [Field Ks] [Field Ω]
    [Algebra K Ks] [Algebra Ks Ω] [Algebra K Ω] [IsScalarTower K Ks Ω] [IsAlgClosed Ω]
    (H : OpenSubgroup (Gal(Ks/K))) (C : PrimaryFixedFieldEquivalence K Ks H)
    (hC : PrimaryFixedFieldComparison K Ks H Ω C)
    (T : Scheme.{u}) (e : Spec (.of (IntermediateField.fixedField H.toSubgroup)) ≅ T)
    (R : Rep.DiscreteContinuousRep.{0, u, u + 1} ℤ (Gal(Ks/K)))
    (A B : AddSubgroup R.obj.V) (hle : A ≤ B)
    (hA : ∀ (g : H.toSubgroup) (x : R.obj.V), x ∈ A →
      R.obj.ρ (g : Gal(Ks/K)) x ∈ A)
    (hB : ∀ (g : H.toSubgroup) (x : R.obj.V), x ∈ B →
      R.obj.ρ (g : Gal(Ks/K)) x ∈ B)
    (htriv : ∀ (g : H.toSubgroup) (x : R.obj.V), x ∈ B →
      R.obj.ρ (g : Gal(Ks/K)) x - x ∈ A) :
    (primarySheafSequence K Ks H Ω C T e R A B hle hA hB).ShortExact ∧
    Nonempty ((primarySheafSequence K Ks H Ω C T e R A B hle hA hB).X₃ ≅
      primaryAssociatedSheaf K Ks H Ω C T e (primaryTrivialQuotient K Ks H R A B)) := by
  let : Module ℤ R.obj.V := AddCommGroup.toIntModule _
  let _keep_hC := hC
  let i := primarySubmoduleInclusion K Ks H R A B hle hA hB
  have hi : Mono i.hom := (Rep.mono_iff_injective i.hom).mpr (by
    intro x y h
    change Submodule.inclusion (AddSubgroup.toIntSubmodule.monotone hle) x =
      Submodule.inclusion (AddSubgroup.toIntSubmodule.monotone hle) y at h
    exact Subtype.ext (congrArg (fun z : B.toIntSubmodule ↦ z.val) h))
  have : Mono i := (ObjectProperty.ι _).mono_of_mono_map hi
  let F := C.inverse ⋙ Etale.upperStar AddCommGrpCat.{u + 1} e.inv
  have : Mono (F.map i) := inferInstance
  constructor
  · change (ShortComplex.mk (F.map i) (cokernel.π (F.map i)) (cokernel.condition _)).ShortExact
    exact { exact := ShortComplex.exact_cokernel (F.map i) }
  · let N := primaryRelativeSubmodule K Ks R A B
    let Q := primaryTrivialQuotient K Ks H R A B
    let q : primarySubmodule K Ks H R B hB ⟶ Q :=
      ObjectProperty.homMk (Rep.ofHom ⟨N.mkQ, fun g ↦ by
        ext x
        change N.mkQ ((primarySubmodule K Ks H R B hB).obj.ρ g x) = N.mkQ x
        apply (Submodule.Quotient.eq N).mpr
        exact htriv g x.val x.property⟩)
    have hiq : i ≫ q = 0 := by
      apply ObjectProperty.hom_ext
      ext x
      exact (Submodule.Quotient.mk_eq_zero N).mpr x.property
    let S := ShortComplex.mk i.hom q.hom
      (congrArg (fun f ↦ f.hom) hiq)
    have hex : S.Exact := by
      let : ∀ X Y : Rep.{u + 1} ℤ H.toSubgroup,
          FunLike (@Representation.IntertwiningMap ℤ H.toSubgroup X Y
            _ _ _ _ X.hV2 Y.hV2 X.ρ Y.ρ) X Y := fun X Y ↦
        @Representation.IntertwiningMap.instFunLike ℤ H.toSubgroup X Y
          _ _ _ _ X.hV2 Y.hV2 X.ρ Y.ρ
      rw [← S.exact_map_iff_of_faithful
        (forget₂ (Rep.{u + 1} ℤ H.toSubgroup) (ModuleCat.{u + 1} ℤ))]
      rw [ShortComplex.moduleCat_exact_iff.{u + 1, 0}]
      change ∀ x : B.toIntSubmodule, N.mkQ x = 0 →
        ∃ y : A.toIntSubmodule,
          Submodule.inclusion (AddSubgroup.toIntSubmodule.monotone hle) y = x
      intro x hx
      exact ⟨⟨x.val, (Submodule.Quotient.mk_eq_zero N).mp hx⟩, Subtype.ext rfl⟩
    have : Epi q.hom := (Rep.epi_iff_surjective q.hom).mpr N.mkQ_surjective
    let c := CokernelCofork.ofπ q hiq
    have hc : IsColimit c := by
      apply isColimitOfReflects (ObjectProperty.ι _)
      exact (CokernelCofork.isColimitMapCoconeEquiv c (ObjectProperty.ι _)).symm
        hex.gIsCokernel
    have hFc := CokernelCofork.mapIsColimit c hc F
    exact ⟨(colimit.isColimit _).coconePointUniqueUpToIso hFc⟩


end AlgebraicGeometry.Scheme
