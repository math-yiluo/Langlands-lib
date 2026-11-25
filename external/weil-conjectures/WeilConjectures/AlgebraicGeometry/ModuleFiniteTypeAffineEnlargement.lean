/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.AlgebraicGeometry.Coherent
import WeilConjectures.AlgebraicGeometry.ModuleFiniteTypeAffineUnion
import WeilConjectures.AlgebraicGeometry.QuasiCoherentExtensionQcOpen
import Mathlib.CategoryTheory.Abelian.Images
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentCokernel

/-! # Enlarging the open of finite type by one affine open

Source: Stacks Project, Properties, Lemma 01PF, proof, lines 2865--2894.
(blueprint: lem-weil-pbc-module-finite-type-affine-enlargement).
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

set_option autoImplicit false

private theorem finiteType_of_affine_enlargement_iso.{u₁, v₁}
    {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}}
    [∀ A, HasSheafify (J.over A) AddCommGrpCat.{u}]
    [∀ A, (J.over A).WEqualsLocallyBijective AddCommGrpCat.{u}]
    {M N : SheafOfModules.{u} R} (e : M ≅ N) [M.IsFiniteType] : N.IsFiniteType := by
  obtain ⟨q, hq⟩ := IsFiniteType.exists_localGeneratorsData M
  let q' : N.LocalGeneratorsData :=
    { I := q.I
      X := q.X
      coversTop := q.coversTop
      generators i := (q.generators i).ofEpi (e.hom.over (q.X i)) }
  refine ⟨q', ⟨fun i ↦ ?_⟩⟩
  exact ⟨(hq.isFiniteType i).finite⟩

set_option backward.isDefEq.respectTransparency false in
/-- A quasi-coherent module finite type on W has a quasi-coherent submodule
finite type on W union V, equal to the original on W, when V is affine.

Source: Stacks Project, Properties, Lemma 01PF, proof, lines 2865--2894.
(blueprint: lem-weil-pbc-module-finite-type-affine-enlargement).

Proof: The overlap W intersect V is quasi-compact by quasi-separatedness. On V,
identify H with the associated sheaf of its module of sections. Cover the overlap
by finitely many principal opens on which H has finitely many generators. Choose
numerators in H(V) for these generators and let N be the submodule they generate.
The associated sheaf of N is a finite-type quasi-coherent submodule of H on V.
Its localization equals H on each principal open: it contains the generators,
and the opposite inclusion follows from N being a submodule of H(V). The affine
quasi-coherent equivalence and the sheaf property identify its restriction to the
whole overlap with H. Glue it with H on W, using the subsheaf of H on W union V
whose sections satisfy both local membership conditions. This subsheaf is
quasi-coherent and finite type, both properties being local. The union is
quasi-compact, and its inclusion into X is quasi-compact since X is
quasi-separated. Extend the inclusion map to X by the quasi-coherent extension
theorem 01PE(3), and take its image in H. Images are quasi-coherent, and restriction
is exact, so this image restricts to the glued submodule on the union. It is
therefore finite type there and its inclusion is an isomorphism on W. If the
overlap is empty the list of generators is empty; all constructions still work.
No quasi-compactness of X or finite type outside W union V is claimed. -/
theorem exists_finiteType_affine_enlargement
    (X : Scheme.{u}) [QuasiSeparatedSpace X]
    (W : X.Opens) (hW : IsCompact (W : Set X)) (V : X.affineOpens)
    (H : SheafOfModules.{u} (moduleRings X.toRingedSpace)) [H.IsQuasicoherent]
    [(H.over W).IsFiniteType] :
    ∃ (E : SheafOfModules.{u} (moduleRings X.toRingedSpace)), E.IsQuasicoherent ∧
      (E.over (W ⊔ V.1)).IsFiniteType ∧ ∃ (j : E ⟶ H),
        Mono j ∧ IsIso ((SheafOfModules.overFunctor
          (moduleRings X.toRingedSpace) W).map j) := by
  let U := W ⊔ V.1
  let R := moduleRings X.toRingedSpace
  let Q := SheafOfModules.overFunctor R U
  let P := SheafOfModules.overFunctor R W
  let T := SheafOfModules.overMap R (homOfLE (show W ≤ U from le_sup_left))
  let η := SheafOfModules.overFunctorMap R (homOfLE (show W ≤ U from le_sup_left))
  have hU : IsCompact (U : Set X) := hW.union V.2.isCompact
  have : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp hU
  obtain ⟨G, hG, hGft, φ, hφ, hφW⟩ := exists_finiteType_affine_union X W hW V H
  have : G.IsQuasicoherent := hG
  have : G.IsFiniteType := hGft
  have : Mono φ := hφ
  have : IsIso (T.map φ) := hφW
  obtain ⟨K, hK, ψ, α, hψ⟩ :=
    exists_quasiCoherent_extension_of_quasiCompact_open X U inferInstance H G φ
  have : K.IsQuasicoherent := hK
  have hψU : Q.map ψ = α.hom ≫ φ := hψ
  have : Mono (Q.map ψ) := by rw [hψU]; infer_instance
  let q := Abelian.factorThruImage ψ
  let j := Abelian.image.ι ψ
  have hqU : Mono (Q.map q) :=
    mono_of_mono_fac (by rw [← Functor.map_comp, Abelian.image.fac])
  have : Q.PreservesEpimorphisms :=
    Functor.preservesEpimorphisms_of_adjunction
      (SheafOfModules.overPushforwardOverAdj (R := R) U)
  have : Epi (Q.map q) := Q.map_epi q
  have : IsIso (Q.map q) := isIso_of_mono_of_epi _
  let e : (Abelian.image ψ).over U ≅ G := (asIso (Q.map q)).symm ≪≫ α
  have hft : ((Abelian.image ψ).over U).IsFiniteType :=
    finiteType_of_affine_enlargement_iso.{u, u, u} e.symm
  have hψW : IsIso (P.map ψ) := by
    apply (NatIso.isIso_map_iff η ψ).mp
    change IsIso (T.map (Q.map ψ))
    rw [hψU, Functor.map_comp]
    infer_instance
  have hqW : IsIso (P.map q) := by
    apply (NatIso.isIso_map_iff η q).mp
    change IsIso (T.map (Q.map q))
    infer_instance
  have hjW : IsIso (P.map j) := by
    have heq : P.map j = inv (P.map q) ≫ P.map ψ := by
      have hfac : P.map q ≫ P.map j = P.map ψ := by
        rw [← Functor.map_comp]
        exact congrArg P.map (Abelian.image.fac ψ)
      rw [← hfac]
      simp only [← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
    rw [heq]
    infer_instance
  have := isQuasicoherent_cokernel ψ
  have himg := isQuasicoherent_kernel (CategoryTheory.Limits.cokernel.π ψ)
  exact ⟨Abelian.image ψ, himg, hft, j, inferInstance, hjW⟩

end AlgebraicGeometry.Scheme.Modules
