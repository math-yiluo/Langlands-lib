import Langlands.Algebra.GroupAlgebraHopfPointLift
import Langlands.GroupScheme.HomScheme.FiniteDiagonalizableHom
import Langlands.GroupScheme.Torus.AffineRelativeDiagonalizable
import Mathlib.RingTheory.Etale.Descent

/-! # Homomorphisms from a finite diagonalizable group into a group of multiplicative type -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme.HomScheme

section BaseChange

variable {S S' : Scheme.{u}} (b : S' ⟶ S) {H G : GroupScheme S}

/-- The comparison between the iterated and the direct base change to an `S'`-scheme. -/
abbrev compIso (T : Over S') (H : GroupScheme S) :
    (baseChange T.hom).obj ((baseChange b).obj H) ≅ (baseChange (T.hom ≫ b)).obj H :=
  Descent.pullbackComparison b T.hom (T.hom ≫ b) rfl H

/-- Homomorphisms over `S` after base change to an `S'`-scheme `T` are homomorphisms over `S'`
between the base changes to `S'`, after base change to `T`. -/
def baseChangeEquiv (T : Over S') :
    RelativeHom H G ((Over.map b).obj T) ≃
      RelativeHom ((baseChange b).obj H) ((baseChange b).obj G) T where
  toFun i := (compIso b T H).hom ≫ i ≫ (compIso b T G).inv
  invFun j := (compIso b T H).inv ≫ j ≫ (compIso b T G).hom
  left_inv i := by simp
  right_inv j := by simp

@[reassoc]
theorem relativeHom_left_snd {T : Over S} (i : RelativeHom H G T) :
    i.hom.hom.left ≫ pullback.snd G.X.hom T.hom = pullback.snd H.X.hom T.hom :=
  Over.w i.hom.hom

@[reassoc]
theorem compIso_hom_left_snd (T : Over S') (H : GroupScheme S) :
    (compIso b T H).hom.hom.hom.left ≫ pullback.snd H.X.hom (T.hom ≫ b) =
      pullback.snd ((baseChange b).obj H).X.hom T.hom :=
  Over.w (compIso b T H).hom.hom.hom

theorem compIso_hom_fst (T : Over S') (H : GroupScheme S) :
    (compIso b T H).hom.hom.hom.left ≫ pullback.fst H.X.hom ((Over.map b).obj T).hom =
      pullback.fst ((baseChange b).obj H).X.hom T.hom ≫ pullback.fst H.X.hom b :=
  Descent.pullbackComparison_hom_fst b T.hom (T.hom ≫ b) rfl H

@[reassoc]
theorem compIso_hom_snd (T : Over S') (H : GroupScheme S) :
    (compIso b T H).hom.hom.hom.left ≫ pullback.snd H.X.hom ((Over.map b).obj T).hom =
      pullback.snd ((baseChange b).obj H).X.hom T.hom :=
  compIso_hom_left_snd b T H

theorem compIso_inv_fst (T : Over S') (G : GroupScheme S) :
    (compIso b T G).inv.hom.hom.left ≫ pullback.fst ((baseChange b).obj G).X.hom T.hom ≫
        pullback.fst G.X.hom b = pullback.fst G.X.hom ((Over.map b).obj T).hom :=
  Descent.pullbackComparison_inv_fst b T.hom (T.hom ≫ b) rfl G

/-- A homomorphism between base changes to `T` lies over `T`, read through the second
projection of the inner base change. -/
@[reassoc]
theorem left_fst_snd {T : Over S'} {H' G' : GroupScheme S}
    (j : (baseChange T.hom).obj ((baseChange b).obj H') ⟶
      (baseChange T.hom).obj ((baseChange b).obj G')) :
    j.hom.hom.left ≫ pullback.fst ((baseChange b).obj G').X.hom T.hom ≫
        pullback.snd G'.X.hom b =
      pullback.snd ((baseChange b).obj H').X.hom T.hom ≫ T.hom := by
  have h2 : pullback.fst ((baseChange b).obj G').X.hom T.hom ≫ pullback.snd G'.X.hom b =
      pullback.snd ((baseChange b).obj G').X.hom T.hom ≫ T.hom := pullback.condition
  rw [h2, ← Category.assoc, relativeHom_left_snd]

theorem compIso_hom_baseChangeProj {T T' : Over S'} (a : T' ⟶ T) (H : GroupScheme S) :
    (compIso b T' H).hom.hom.hom.left ≫ baseChangeProj H ((Over.map b).map a) =
      baseChangeProj ((baseChange b).obj H) a ≫ (compIso b T H).hom.hom.hom.left := by
  apply pullback.hom_ext
  · rw [Category.assoc, baseChangeProj_fst, compIso_hom_fst, Category.assoc, compIso_hom_fst,
      baseChangeProj_fst_assoc]
  · rw [Category.assoc, baseChangeProj_snd, compIso_hom_snd_assoc, Category.assoc,
      compIso_hom_snd, baseChangeProj_snd]
    rfl

theorem baseChangeEquiv_evaluate {T T' : Over S'} (a : T' ⟶ T)
    (i : RelativeHom H G ((Over.map b).obj T)) :
    baseChangeEquiv b T' (evaluate ((Over.map b).map a) i) =
      evaluate a (baseChangeEquiv b T i) := by
  apply relativeHom_ext
  rw [evaluate_fst]
  apply pullback.hom_ext
  · simp only [baseChangeEquiv, Equiv.coe_fn_mk, Grp.comp_hom_hom, Over.comp_left,
      Category.assoc]
    rw [compIso_inv_fst, compIso_inv_fst, evaluate_fst, ← Category.assoc,
      compIso_hom_baseChangeProj, Category.assoc]
  · rw [Category.assoc, left_fst_snd, Category.assoc, Category.assoc, left_fst_snd,
      baseChangeProj_snd_assoc, Over.w a]

end BaseChange

section Etale

open Langlands.FiniteBialgebraHom FiniteSource FiniteDiagonalizable

variable {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R']

variable (R R') in
/-- The base map `Spec R' ⟶ Spec R`. -/
abbrev specBase : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R R'))

/-- For an `R'`-algebra `B` with compatible `R`-algebra structure, `Spec B` over `Spec R` is
`Spec B` over `Spec R'`, viewed over `Spec R`. -/
def specOverIso (B : Type u) [CommRing B] [Algebra R B] [Algebra R' B]
    [IsScalarTower R R' B] :
    (Over.map (specBase R R')).obj (specOver R' B) ≅ specOver R B :=
  Over.isoMk (Iso.refl _) (by
    simp only [specOver, Over.map_obj_hom, Over.mk_hom, Iso.refl_hom, Category.id_comp,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq])

theorem specOverIso_naturality {B C : Type u} [CommRing B] [Algebra R B] [Algebra R' B]
    [IsScalarTower R R' B] [CommRing C] [Algebra R C] [Algebra R' C] [IsScalarTower R R' C]
    (g : B →ₐ[R'] C) :
    (Over.map (specBase R R')).map (specMap g) ≫ (specOverIso B).hom =
      (specOverIso C).hom ≫ specMap (g.restrictScalars R) := by
  apply Over.OverMorphism.ext
  simp only [specOverIso, Over.comp_left, Over.map_map_left, Over.isoMk_hom_left, Iso.refl_hom,
    Category.comp_id, Category.id_comp]
  rfl

/-- Evaluation along an isomorphism of test objects is a bijection of families. -/
def evaluateEquiv {S : Scheme.{u}} {H G : GroupScheme S} {T T' : Over S} (e : T' ≅ T) :
    RelativeHom H G T ≃ RelativeHom H G T' where
  toFun := evaluate e.hom
  invFun := evaluate e.inv
  left_inv i := by rw [← evaluate_comp, e.inv_hom_id, evaluate_id]
  right_inv i := by rw [← evaluate_comp, e.hom_inv_id, evaluate_id]

variable (R R') in
/-- The group algebra source over `R'` is the base change of the group algebra source over
`R`. -/
def sourceIso (A : Type u) [AddCommGroup A] :
    hopfGroup R' (AddMonoidAlgebra R' A) ≅
      (baseChange (specBase R R')).obj (hopfGroup R (AddMonoidAlgebra R A)) :=
  Diagonalizable.hopfSpecIso (CommRingCat.of R') A ≪≫
    Diagonalizable.relativeModelIso (CommRingCat.of R') A ≪≫
    (RelativeMultiplicativeType.diagonalizableBaseChangeIso (specBase R R') A).symm ≪≫
    (baseChange (specBase R R')).mapIso
      (Diagonalizable.hopfSpecIso (CommRingCat.of R) A ≪≫
        Diagonalizable.relativeModelIso (CommRingCat.of R) A).symm

/-- A splitting of `G` over `R'` identifies the base change of its coordinate Hopf spectrum
with the group algebra spectrum over `R'`. -/
def targetIso (G : GroupScheme (Spec (CommRingCat.of R))) [IsAffine G.X.left]
    {Λ : Type u} [AddCommGroup Λ]
    (ψ : (baseChange (specBase R R')).obj G ≅
      RelativeMultiplicativeType.diagonalizable (Spec (CommRingCat.of R')) Λ) :
    (baseChange (specBase R R')).obj (hopfGroup R (AffineCoordinates.hopfAlgebra G)) ≅
      hopfGroup R' (AddMonoidAlgebra R' Λ) :=
  (baseChange (specBase R R')).mapIso (coordinateIso G) ≪≫ ψ ≪≫
    (Diagonalizable.relativeModelIso (CommRingCat.of R') Λ).symm ≪≫
    (Diagonalizable.hopfSpecIso (CommRingCat.of R') Λ).symm

end Etale

section EtaleChain

open Langlands.FiniteBialgebraHom FiniteSource FiniteDiagonalizable

variable {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R']
  (G : GroupScheme (Spec (CommRingCat.of R))) [IsAffine G.X.left]
  [Algebra.FinitePresentation R (AffineCoordinates.hopfAlgebra G)]
  {Λ : Type u} [AddCommGroup Λ]
  (ψ : (baseChange (specBase R R')).obj G ≅
    RelativeMultiplicativeType.diagonalizable (Spec (CommRingCat.of R')) Λ)
  (A : Type u) [AddCommGroup A] [Fintype A]

/-- Algebra maps out of the base-changed Hom algebra are Hopf points over `R'` from the split
target into the group algebra source. -/
def pointChain (B : Type u) [CommRing B] [Algebra R B] [Algebra R' B] [IsScalarTower R R' B] :
    (R' ⊗[R] HomAlgebra R (AffineCoordinates.hopfAlgebra G) (AddMonoidAlgebra R A) →ₐ[R'] B) ≃
      {f : AddMonoidAlgebra R' Λ →ₐ[R'] B ⊗[R'] AddMonoidAlgebra R' A // IsHopfPoint R' f} :=
  (AlgHom.liftEquiv R R' _ B).symm.trans <|
    (homEquiv R _ _ B).trans <|
    (pointEquiv _ _ B).symm.trans <|
    (evaluateEquiv (specOverIso B)).trans <|
    (baseChangeEquiv (specBase R R') (specOver R' B)).trans <|
    (transportEquiv (sourceIso R R' A) (targetIso G ψ) (specOver R' B)).trans <|
    pointEquiv _ _ B


theorem pointChain_naturality {B C : Type u} [CommRing B] [Algebra R B] [Algebra R' B]
    [IsScalarTower R R' B] [CommRing C] [Algebra R C] [Algebra R' C] [IsScalarTower R R' C]
    (g : B →ₐ[R'] C)
    (φ : R' ⊗[R] HomAlgebra R (AffineCoordinates.hopfAlgebra G) (AddMonoidAlgebra R A) →ₐ[R'] B) :
    (pointChain G ψ A C (g.comp φ)).1 = pushPoint R' g (pointChain G ψ A B φ).1 := by
  simp only [pointChain, Equiv.trans_apply, evaluateEquiv, transportEquiv, Equiv.coe_fn_mk]
  have h1 : (AlgHom.liftEquiv R R' _ C).symm (g.comp φ) =
      (g.restrictScalars R).comp ((AlgHom.liftEquiv R R' _ B).symm φ) :=
    AlgHom.ext fun _ => rfl
  rw [h1]
  generalize (AlgHom.liftEquiv R R' _ B).symm φ = x
  have h2 : homEquiv R _ _ C ((g.restrictScalars R).comp x) =
      ⟨pushPoint R (g.restrictScalars R) (homEquiv R _ _ B x).1,
        (homEquiv R _ _ B x).2.pushPoint R _⟩ :=
    Subtype.ext (pushPoint_pushPoint R _ _ _).symm
  rw [h2, ← evaluate_specMap]
  generalize (pointEquiv _ _ B).symm (homEquiv R _ _ B x) = y
  rw [← evaluate_comp, ← specOverIso_naturality, evaluate_comp]
  generalize evaluate (specOverIso (R := R) (R' := R') B).hom y = z
  rw [baseChangeEquiv_evaluate]
  generalize baseChangeEquiv (specBase R R') (specOver R' B) z = w
  rw [← evaluate_transport]
  generalize transport (sourceIso R R' A) (targetIso G ψ) w = v
  rw [← (pointEquiv _ _ B).symm_apply_apply v, evaluate_specMap, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply]

include ψ in
/-- After a faithfully flat base change splitting the target, the Hom algebra is formally
étale: Hopf points into a group algebra lift uniquely along square-zero thickenings. -/
theorem formallyEtale_tensor_homAlgebra :
    Algebra.FormallyEtale R'
      (R' ⊗[R] HomAlgebra R (AffineCoordinates.hopfAlgebra G) (AddMonoidAlgebra R A)) := by
  classical
  rw [Algebra.FormallyEtale.iff_comp_bijective]
  intro B _ _ I hI
  let : Algebra R B := Algebra.compHom B (algebraMap R R')
  have : IsScalarTower R R' B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hnil : ∀ x ∈ RingHom.ker ((Ideal.Quotient.mkₐ R' I : B →ₐ[R'] B ⧸ I) : B →+* B ⧸ I),
      IsNilpotent x := by
    intro x hx
    have hx' : x ∈ I := by
      rw [RingHom.mem_ker] at hx
      exact Ideal.Quotient.eq_zero_iff_mem.mp hx
    refine ⟨2, ?_⟩
    have : x ^ 2 ∈ I ^ 2 := Ideal.pow_mem_pow hx' 2
    rwa [hI, Ideal.mem_bot] at this
  have h : ((Ideal.Quotient.mkₐ R' I).comp :
        (R' ⊗[R] HomAlgebra R (AffineCoordinates.hopfAlgebra G) (AddMonoidAlgebra R A) →ₐ[R'] B) →
          _) =
      (pointChain G ψ A (B ⧸ I)).symm ∘
        (fun f => ⟨pushPoint R' (Ideal.Quotient.mkₐ R' I) f.1, f.2.pushPoint R' _⟩) ∘
          pointChain G ψ A B := by
    funext φ
    simp only [Function.comp_apply]
    rw [Equiv.eq_symm_apply]
    exact Subtype.ext (pointChain_naturality G ψ A _ φ)
  rw [h]
  exact (pointChain G ψ A _).symm.bijective.comp
    ((bijective_pushPoint hnil (Ideal.Quotient.mkₐ_surjective R' I) Λ).comp
      (pointChain G ψ A B).bijective)

end EtaleChain

section EtaleHomAlgebra

open Langlands.FiniteBialgebraHom FiniteSource FiniteDiagonalizable

/-- **Étaleness of homomorphisms into a group of multiplicative type.** Let `G` be an affine
group of finite presentation over `Spec R` that becomes diagonalizable after a faithfully flat
base change `R → R'`. For a finite abelian group `A`, the algebra representing homomorphisms
from the diagonalizable group `D(A)` to `G` is étale over `R`. -/
theorem etale_homAlgebra {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R']
    [Module.FaithfullyFlat R R'] (G : GroupScheme (Spec (CommRingCat.of R)))
    [IsAffine G.X.left] [LocallyOfFinitePresentation G.X.hom] {Λ : Type u} [AddCommGroup Λ]
    (ψ : (baseChange (specBase R R')).obj G ≅
      RelativeMultiplicativeType.diagonalizable (Spec (CommRingCat.of R')) Λ)
    (A : Type u) [AddCommGroup A] [Fintype A] :
    Algebra.Etale R (HomAlgebra R (AffineCoordinates.hopfAlgebra G) (AddMonoidAlgebra R A)) := by
  have := formallyEtale_tensor_homAlgebra G ψ A
  have : Algebra.Etale R'
      (R' ⊗[R] HomAlgebra R (AffineCoordinates.hopfAlgebra G) (AddMonoidAlgebra R A)) := {}
  exact Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat R'

end EtaleHomAlgebra

end Langlands.GroupScheme.HomScheme
