/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.GroupTheory.PGroup
public import WeilConjectures.AlgebraicGeometry.Sites.EtaleTorsion
import WeilConjectures.AlgebraicGeometry.EtaleSheafDiscreteContinuousRep
import WeilConjectures.RepresentationTheory.FinitePrimaryDecomposition
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Primary summands of a finite generic sheaf

Source: blueprint `theorem-cohomology-curves--2`, proof paragraph 1.
(blueprint: lem-sc-generic-finite-primary-decomposition)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits ZeroObject

namespace AlgebraicGeometry.Scheme

/-- An abelian sheaf on a field with finite geometric stalk (hence torsion) has finitely many
primary summands, with projection and inclusion maps whose composites sum to the identity.
Only the geometric stalks are asserted finite; no curve, extension, filtration or cohomology
is involved.

Source: blueprint `theorem-cohomology-curves--2`, proof paragraph 1.

Proof: take a separable closure of K inside its algebraic closure. Apply the abelian
stalk/Galois-module equivalence to M. The resulting finite abelian group V has an
annihilating integer N, for example its cardinality. If V is zero, take r = 0; the
identity of the zero sheaf is the empty sum. Otherwise enumerate the prime divisors of N
as p_i and write N as the product of the pairwise coprime powers q_i = p_i ^ v_i(N).
The subgroup V_i killed by q_i is invariant under every group automorphism, hence under
Galois. Chinese remainder gives integers c_i with c_i = 1 modulo q_i and c_i = 0 modulo
q_j for j different from i. Multiplication by c_i is the equivariant projection onto V_i:
q_i c_i kills V, it fixes V_i, and the sum of the c_i is 1 modulo N. The inclusion and
projection therefore have sum of composites equal to identity. Each V_i is finite, and
every element has order a power of p_i. Restrict the continuous discrete action to V_i.
Transport these submodules and maps through the quasi-inverse of the equivalence, then
conjugate with its unit isomorphism at M. Additivity transports the sum identity, and
the stalk comparison transports finiteness and the p-group condition. The prime field
and all summands stay in the original coefficient universe; no field extension is chosen.
(blueprint: lem-sc-generic-finite-primary-decomposition) -/
theorem exists_finite_primary_sheaf_decomposition
    (K : Type u) [Field K]
    (M : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (hfinite : Finite (((pointSmallEtale
      (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))))).sheafFiber
        (A := AddCommGrpCat.{u + 1})).obj M)) :
    ∃ (r : ℕ) (p : Fin r → ℕ)
      (N : Fin r → Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1}),
      (∀ i, (p i).Prime) ∧
      (∀ i, Finite (((pointSmallEtale
        (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))))).sheafFiber
          (A := AddCommGrpCat.{u + 1})).obj (N i))) ∧
      (∀ i, IsPGroup (p i) (Multiplicative (((pointSmallEtale
        (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))))).sheafFiber
          (A := AddCommGrpCat.{u + 1})).obj (N i)))) ∧
      ∃ (a : ∀ i, M ⟶ N i) (b : ∀ i, N i ⟶ M),
        ∑ i, a i ≫ b i = 𝟙 M := by
  classical
  let Ks := SeparableClosure K
  let E := etaleSheafEquivDiscreteContinuousRep K Ks
  let i := etaleSheafEquivDiscreteContinuousRepForgetIso K Ks (AlgebraicClosure K)
  let U : Rep.DiscreteContinuousRep.{0, u, u + 1} ℤ (Gal(Ks/K)) ⥤
      AddCommGrpCat.{u + 1} :=
    ObjectProperty.ι _ ⋙ Rep.RepToAction ℤ (Gal(Ks/K)) ⋙
      Action.forget (ModuleCat.{u + 1} ℤ) (Gal(Ks/K)) ⋙
      forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat
  let V := E.functor.obj M
  have hV : Finite V.obj.V := by
    exact Finite.of_injective (i.hom.app M) (ConcreteCategory.bijective_of_isIso _).1
  let := hV
  obtain ⟨r, p, N, hp, hNfinite, hNprimary, a, b, hab⟩ :=
    Rep.exists_finite_primary_decomposition (Gal(Ks/K)) V
  let e (t : Fin r) :=
    (i.app (E.inverse.obj (N t))).symm ≪≫ U.mapIso (E.counitIso.app (N t))
  refine ⟨r, p, fun t ↦ E.inverse.obj (N t), hp, ?_, ?_, ?_⟩
  · intro t
    have : Finite (U.obj ((𝟭 _).obj (N t))) := hNfinite t
    exact Finite.of_injective (e t).hom (ConcreteCategory.bijective_of_isIso _).1
  · intro t
    exact (hNprimary t).of_injective (e t).hom.hom.toMultiplicative
      (ConcreteCategory.bijective_of_isIso (e t).hom).1
  · have : E.functor.Additive := Functor.additive_of_preserves_binary_products _
    let η := E.unitIso.app M
    refine ⟨fun t ↦ η.hom ≫ E.inverse.map (a t),
      fun t ↦ E.inverse.map (b t) ≫ η.inv, ?_⟩
    calc
      _ = η.hom ≫ E.inverse.map (∑ t, a t ≫ b t) ≫ η.inv := by
        rw [E.inverse.map_sum]
        simp only [Functor.map_comp, Preadditive.comp_sum, Preadditive.sum_comp,
          Category.assoc]
      _ = 𝟙 M := by rw [hab, E.inverse.map_id]; simp

end AlgebraicGeometry.Scheme
