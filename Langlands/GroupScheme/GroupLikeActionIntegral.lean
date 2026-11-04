import Langlands.GroupScheme.GroupLikeActionRigidity
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Rigidity of actions with integral affine acting group -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.AutomorphicAction

attribute [local instance] coefficientAlgebra coefficientTower

variable {k R : Type u} [Field k] [CommRing R] [Algebra k R]
    {C : CommHopfAlgCat.{u} (CommRingCat.of k)}
    {H : GroupScheme (Spec (CommRingCat.of k))}

/-- A field algebra becomes a parameter algebra through the supplied map. -/
def parameterAlgebra (A : CommAlgCat.{u} (CommRingCat.of k)) (f : R →ₐ[k] A) :
    CommAlgCat.{u} (CommRingCat.of R) :=
  @CommAlgCat.of R _ A _ f.toRingHom.toAlgebra

/-- The composite field algebra of a parameter algebra recovers the original
field algebra by the identity on the underlying ring. -/
def coefficientOriginalIso (A : CommAlgCat.{u} (CommRingCat.of k)) (f : R →ₐ[k] A) :
    fieldCoefficients (k := k) (parameterAlgebra A f) ≅ A :=
  { hom := ConcreteCategory.ofHom (C := CommAlgCat (CommRingCat.of k))
      (@AlgHom.mk k A A _ _ _ (coefficientAlgebra (parameterAlgebra A f)) A.algebra
        (RingHom.id A) (fun r => f.commutes r))
    inv := ConcreteCategory.ofHom (C := CommAlgCat (CommRingCat.of k))
      (@AlgHom.mk k A A _ _ _ A.algebra (coefficientAlgebra (parameterAlgebra A f))
        (RingHom.id A) (fun r => (f.commutes r).symm))
    hom_inv_id := by apply CommAlgCat.hom_ext; apply DFunLike.ext; intro r; rfl
    inv_hom_id := by apply CommAlgCat.hom_ext; apply DFunLike.ext; intro r; rfl }

variable (hspan : Submodule.span k {c : C | IsGroupLikeElem k c} = ⊤)
    (a : AutomorphicAction H ((hopfSpec (CommRingCat.of k)).obj (op C)))
    (s : (algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of k R)) ⟶ H.X)

include hspan in
/-- Integral-parameter rigidity on an arbitrary affine test equipped with a
map from the parameter algebra. -/
theorem act_affine_eq_self_of_specialization [IsDomain R] (ε : R →ₐ[k] k)
    (hs : specializationSpecMap ε ≫ s = 1)
    (A : CommAlgCat.{u} (CommRingCat.of k)) (f : R →ₐ[k] A)
    (x : (algSpec (CommRingCat.of k)).obj (op A) ⟶
      ((hopfSpec (CommRingCat.of k)).obj (op C)).X) :
    a.act ((algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom f).op ≫ s) x = x := by
  let AR := parameterAlgebra A f
  let e := coefficientOriginalIso A f
  let b := (algSpec (CommRingCat.of k)).mapIso e.op
  have hb : b.hom ≫ parameterSpecMap (k := k) AR =
      (algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom f).op := by
    change (algSpec (CommRingCat.of k)).map e.hom.op ≫
      (algSpec (CommRingCat.of k)).map
        (CommAlgCat.ofHom (IsScalarTower.toAlgHom k R AR)).op = _
    rw [← Functor.map_comp]
    apply congrArg (algSpec (CommRingCat.of k)).map
    apply Quiver.Hom.unop_inj
    apply CommAlgCat.hom_ext
    apply DFunLike.ext
    intro r
    rfl
  have ht := act_parameter_eq_self_of_specialization hspan a s ε hs AR (b.inv ≫ x)
  have he := congrArg (fun z => b.hom ≫ z) ht
  rw [a.naturality, ← Category.assoc, hb] at he
  simpa only [Iso.hom_inv_id_assoc] using he

variable {D : CommHopfAlgCat.{u} (CommRingCat.of k)}

include hspan in
/-- An integral Hopf-spectrum acting group acts trivially on every affine test
of a group-like-spanned target. -/
theorem act_affine_eq_self_of_integral_actor [IsDomain D]
    (a : AutomorphicAction ((hopfSpec (CommRingCat.of k)).obj (op D))
      ((hopfSpec (CommRingCat.of k)).obj (op C)))
    (A : CommAlgCat.{u} (CommRingCat.of k))
    (h : (algSpec (CommRingCat.of k)).obj (op A) ⟶
      ((hopfSpec (CommRingCat.of k)).obj (op D)).X)
    (x : (algSpec (CommRingCat.of k)).obj (op A) ⟶
      ((hopfSpec (CommRingCat.of k)).obj (op C)).X) : a.act h x = x := by
  let s := HopfSpecPoints.specPoint (R := CommRingCat.of k)
    (A := D) (Y := CommAlgCat.of k D) (AlgHom.id k D)
  have hs : specializationSpecMap (Bialgebra.counitAlgHom k D) ≫ s = 1 := by
    have he := HopfSpecPoints.specPoint_precomp (R := CommRingCat.of k)
      (C := D) (A := CommAlgCat.of k D) (B := CommAlgCat.of k k)
      (Bialgebra.counitAlgHom k D) (AlgHom.id k D)
    change specializationSpecMap (Bialgebra.counitAlgHom k D) ≫ s = _ at he
    rw [he]
    simpa only [AlgHom.comp_id, Algebra.ofId_self, AlgHom.id_comp] using
      (HopfSpecPoints.specPoint_one (R := CommRingCat.of k)
        (A := D) (Y := CommAlgCat.of k k)).symm
  obtain ⟨f, rfl⟩ := HopfSpecPoints.exists_specPoint h
  have ht := act_affine_eq_self_of_specialization hspan a s
    (Bialgebra.counitAlgHom k D) hs A f x
  have he := HopfSpecPoints.specPoint_precomp (R := CommRingCat.of k)
    (C := D) (A := CommAlgCat.of k D) (B := A) f (AlgHom.id k D)
  change (algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom f).op ≫ s = _ at he
  rw [he, AlgHom.comp_id] at ht
  exact ht

include hspan in
/-- The action morphism of an integral Hopf-spectrum actor is projection. -/
theorem hom_eq_snd_of_integral_actor [IsDomain D]
    (a : AutomorphicAction ((hopfSpec (CommRingCat.of k)).obj (op D))
      ((hopfSpec (CommRingCat.of k)).obj (op C))) :
    a.hom = snd _ _ := by
  have : IsAffine ((hopfSpec (CommRingCat.of k)).obj (op D)).X.left :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of D)))
  have : IsAffine ((hopfSpec (CommRingCat.of k)).obj (op C)).X.left :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of C)))
  let P := ((hopfSpec (CommRingCat.of k)).obj (op D)).X ⊗
    ((hopfSpec (CommRingCat.of k)).obj (op C)).X
  have hp : (algSpec (CommRingCat.of k)).essImage P := by
    rw [essImage_algSpec]
    change IsAffine (Limits.pullback _ _)
    infer_instance
  let e := hp.getIso
  apply (cancel_epi e.hom).mp
  have ht := act_affine_eq_self_of_integral_actor hspan a hp.witness.unop
    (e.hom ≫ fst _ _) (e.hom ≫ snd _ _)
  simpa only [act, lift_comp_fst_snd] using ht

include hspan in
/-- An integral Hopf-spectrum acting group acts trivially on all scheme tests. -/
theorem act_eq_self_of_integral_actor [IsDomain D]
    (a : AutomorphicAction ((hopfSpec (CommRingCat.of k)).obj (op D))
      ((hopfSpec (CommRingCat.of k)).obj (op C)))
    {T : Over (Spec (CommRingCat.of k))}
    (h : T ⟶ ((hopfSpec (CommRingCat.of k)).obj (op D)).X)
    (x : T ⟶ ((hopfSpec (CommRingCat.of k)).obj (op C)).X) : a.act h x = x := by
  rw [act, hom_eq_snd_of_integral_actor hspan a, lift_snd]

end Langlands.GroupScheme.AutomorphicAction
