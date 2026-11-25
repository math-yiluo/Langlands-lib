/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.FieldTheory.PurelyInseparable.Basic
import WeilConjectures.AlgebraicGeometry.ReducedGenericFibreMapCore
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Topology
namespace AlgebraicGeometry
/-- Core affine construction of the dominant map, omitting separable generation.
Source: Stacks Project, Tags 0559 and 030R; the affine tensor and reduction argument.
Proof: give E its residue-field algebra structure by composing e with k' -> E.
Write A, B, B' for the affine coordinate rings of Z, S, S', and k = kappa(eta).
The ring C of the original fibre is A tensor_B k. Dominance of j makes C -> L
injective, and its base identity says that this map is k-linear. Tensor with the
flat k-module k' to obtain an injection C tensor_k k' -> L tensor_k k'. The two
maps to E induce a unital map L tensor_k k' -> E by hsquare. The latter tensor
ring is finite-dimensional over L and has a single prime: purely inseparable
field extension induces a homeomorphism on spectra. Thus the kernel of its map
to the field E is its nilradical. The induced map on its reduction is injective.
The first injection induces an injection on reductions, since an element whose
image is nilpotent is itself nilpotent. Hence (C tensor_k k')_red embeds in E.
The coordinate ring of the reduced pullback is (A tensor_B B')_red. Since B'
is a domain and eta' is generic, kappa(eta') is its fraction field. Localizing
at the nonzero elements of B' commutes with reduction. Via hq and he this
identifies the reduced pullback's generic fibre ring with (C tensor_k k')_red.
Take the spectrum of the constructed injection. It is scheme-theoretically
dominant; the scalar-map identity and the compatibility with e follow from the
chosen algebra map and the tensor-product construction. This also proves the
identity-extension case, and requires no separability hypothesis on E.
(blueprint: lem-sbc-reduced-generic-fibre-field-embedding-core) -/
theorem exists_reduced_generic_fibre_field_embedding_core
    {Z S S' : Scheme.{u}} [IsAffine Z] [IsAffine S] [IsAffine S'] [IsIntegral S']
    (g : Z ⟶ S) (q : S' ⟶ S) (η : S) (η' : S') (hq : q η' = η)
    (hη' : IsGenericPoint η' Set.univ)
    (L k' E : Type u) [Field L] [Field k'] [Field E]
    [Algebra (S.residueField η) L] [Algebra (S.residueField η) k']
    [Algebra L E] [Algebra k' E]
    [Module.Finite (S.residueField η) k'] [IsPurelyInseparable (S.residueField η) k']
    (j : Spec (.of L) ⟶ g.fiber η) (hj : IsSchemeTheoreticallyDominant j)
    (hjbase : j ≫ g.fiberToSpecResidueField η =
      Spec.map (CommRingCat.ofHom (algebraMap (S.residueField η) L)))
    (e : S'.residueField η' ≃+* k')
    (he : e.toRingHom.comp
      (((S.residueFieldCongr hq).inv ≫ q.residueFieldMap η').hom) =
        algebraMap (S.residueField η) k')
    (hsquare : (algebraMap k' E).comp (algebraMap (S.residueField η) k') =
      (algebraMap L E).comp (algebraMap (S.residueField η) L)) :
    ∃ aE : Algebra (S'.residueField η') E,
      letI := aE
      ∃ h : Spec (.of E) ⟶
          ((pullback g q).nilradical.subschemeι ≫ pullback.snd g q).fiber η',
        IsSchemeTheoreticallyDominant h ∧
        h ≫ ((pullback g q).nilradical.subschemeι ≫
          pullback.snd g q).fiberToSpecResidueField η' =
            Spec.map (CommRingCat.ofHom (algebraMap (S'.residueField η') E)) ∧
        ∀ x : S'.residueField η',
          algebraMap (S'.residueField η') E x = algebraMap k' E (e x) := by
  let aE : Algebra (S'.residueField η') E :=
    ((algebraMap k' E).comp e.toRingHom).toAlgebra
  obtain ⟨h, hh, hb⟩ := exists_reduced_generic_fibre_map_core
    g q η η' hq hη' L k' E j hj hjbase e he hsquare aE rfl
  refine ⟨aE, ?_⟩
  let _ := aE
  refine ⟨h, hh, hb, ?_⟩
  intro x
  rfl
end AlgebraicGeometry
