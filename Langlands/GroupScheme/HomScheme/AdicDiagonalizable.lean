import Langlands.Algebra.AdicHopfPoint
import Langlands.GroupScheme.HomScheme.AdicSystem
import Langlands.GroupScheme.HomScheme.FiniteSourceHom
import Langlands.GroupScheme.HopfMorphismBaseChange
import Langlands.GroupScheme.AffineHopfCoordinates
import Langlands.GroupScheme.Torus.AffineRelativeDiagonalizable
import Langlands.GroupScheme.Torus.DiagonalizableHopf

/-! # Adic effectivity for homomorphisms from diagonalizable Hopf spectra -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.HomScheme.AdicDiagonalizable

open Langlands.Algebra.HopfPointBridge
open Langlands.AlgebraicGeometry.AdicAffinePoints
open Langlands.FiniteBialgebraHom
open FiniteSource

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {A : Type u} [CommRing A] {C : Type u} [CommRing C] [HopfAlgebra A C]
variable {M : Type u} [AddCommGroup M]

/-- The coordinate Hopf point of a pulled-back homomorphism is the pushed point. -/
theorem point_evaluate_specMap {Q D : Type u} [CommRing Q] [Algebra A Q]
    [CommRing D] [Algebra A D] (g : Q →ₐ[A] D)
    (f : RelativeHom (hopfGroup A (AddMonoidAlgebra A M)) (hopfGroup A C) (specOver A Q)) :
    ((pointEquiv C (AddMonoidAlgebra A M) D) (evaluate (specMap g) f)).1 =
      pushPoint A g ((pointEquiv C (AddMonoidAlgebra A M) Q) f).1 := by
  have h := evaluate_specMap g ((pointEquiv C (AddMonoidAlgebra A M) Q) f)
  rw [Equiv.symm_apply_apply] at h
  rw [h, Equiv.apply_symm_apply]

set_option maxHeartbeats 800000 in
/-- The relative Hopf coordinates of an actual scalar-extended homomorphism. -/
theorem relativeHomEquiv_baseChange (Q : Type u) [CommRing Q] [Algebra A Q]
    (g : C →ₐc[A] AddMonoidAlgebra A M) :
    relativeHomEquiv C (AddMonoidAlgebra A M) Q
      ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap A Q)))).map
        ((hopfSpec (CommRingCat.of A)).map (CommHopfAlgCat.ofHom g).op)) =
      Bialgebra.TensorProduct.map (BialgHom.id Q Q) g := by
  apply (relativeHomEquiv C (AddMonoidAlgebra A M) Q).symm.injective
  rw [Equiv.symm_apply_apply]
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  exact HopfMorphismBaseChange.tensorSpecIso_naturality g.toAlgHom

set_option maxHeartbeats 800000 in
/-- In group-algebra coordinates, actual base change is coefficientwise change of ring. -/
theorem groupPoint_baseChange (Q : Type u) [CommRing Q] [Algebra A Q]
    (g : C →ₐc[A] AddMonoidAlgebra A M) :
    toGroupAlgebra ((pointEquiv C (AddMonoidAlgebra A M) Q)
      ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap A Q)))).map
        ((hopfSpec (CommRingCat.of A)).map (CommHopfAlgCat.ofHom g).op))).1 =
      (AddMonoidAlgebra.mapAlgHom M (Algebra.ofId A Q)).comp g.toAlgHom := by
  apply AlgHom.ext
  intro x
  change Langlands.Algebra.HopfPointBridge.scalarMap A Q M
    ((bialgHomEquiv A (relativeHomEquiv C (AddMonoidAlgebra A M) Q _)).1 x) = _
  rw [relativeHomEquiv_baseChange]
  simp [bialgHomEquiv_apply_coe, Langlands.Algebra.HopfPointBridge.scalarMap]

variable (I : Ideal A)

/-- A formal homomorphism system expressed in the published native Hopf-point coordinates. -/
def nativePoint
    (s : Adic.System I (hopfGroup A (AddMonoidAlgebra A M)) (hopfGroup A C)) (n : ℕ) :
    {f : C →ₐ[A] (A ⧸ I ^ (n + 1)) ⊗[A] AddMonoidAlgebra A M // IsHopfPoint A f} :=
  (pointEquiv C (AddMonoidAlgebra A M) (A ⧸ I ^ (n + 1))) (s.hom n)

/-- The same formal homomorphism in group-algebra coordinates. -/
def groupPoint
    (s : Adic.System I (hopfGroup A (AddMonoidAlgebra A M)) (hopfGroup A C)) (n : ℕ) :
    C →ₐ[A] AddMonoidAlgebra (A ⧸ I ^ (n + 1)) M :=
  toGroupAlgebra (nativePoint I s n).1

set_option maxHeartbeats 800000 in
/-- Successive compatibility of the group-algebra coefficient maps. -/
theorem groupPoint_compatible
    (s : Adic.System I (hopfGroup A (AddMonoidAlgebra A M)) (hopfGroup A C))
    (n : ℕ) (x : C) (m : M) :
    Ideal.Quotient.factorPow I (n + 1).le_succ ((groupPoint I s (n + 1) x).coeff m) =
      (groupPoint I s n x).coeff m := by
  let q : (A ⧸ I ^ (n + 1 + 1)) →ₐ[A] A ⧸ I ^ (n + 1) :=
    Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right (n + 1).le_succ)
  have hn := point_evaluate_specMap q (s.hom (n + 1))
  have hs := s.compatible n
  change evaluate (specMap q) (s.hom (n + 1)) = s.hom n at hs
  rw [hs] at hn
  have he := congrArg toGroupAlgebra hn
  rw [toGroupAlgebra_pushPoint] at he
  have hc := congrArg (fun f : C →ₐ[A] AddMonoidAlgebra (A ⧸ I ^ (n + 1)) M =>
    (f x).coeff m) he.symm
  simpa only [q, groupPoint, nativePoint, AlgHom.comp_apply,
    AddMonoidAlgebra.coeff_mapAlgHom, Ideal.Quotient.factorₐ_apply] using hc

/-- The coefficient-algebra system attached to a formal scheme homomorphism. -/
def algebraSystem
    (s : Adic.System I (hopfGroup A (AddMonoidAlgebra A M)) (hopfGroup A C)) :
    Langlands.AdicHopfPoint.System I (C := C) (M := M) :=
  Langlands.AdicHopfPoint.System.ofSucc (groupPoint I s)
    (fun n => (isHopfPoint_iff (nativePoint I s n).1).mp (nativePoint I s n).2)
    (groupPoint_compatible I s)

variable [IsNoetherianRing A] [IsAdicComplete I A]

/-- The genuine global homomorphism algebraizing a formal homomorphism system. -/
def lift
    (s : Adic.System I (hopfGroup A (AddMonoidAlgebra A M)) (hopfGroup A C)) :
    hopfGroup A (AddMonoidAlgebra A M) ⟶ hopfGroup A C :=
  (hopfSpec (CommRingCat.of A)).map (CommHopfAlgCat.ofHom (algebraSystem I s).lift).op

/-- Every reduction of the constructed homomorphism is the prescribed formal one. -/
theorem lift_reduction
    (s : Adic.System I (hopfGroup A (AddMonoidAlgebra A M)) (hopfGroup A C)) (n : ℕ) :
    (baseChange (quotientMap I n)).map (lift I s) = s.hom n := by
  apply (pointEquiv C (AddMonoidAlgebra A M) (A ⧸ I ^ (n + 1))).injective
  apply Subtype.ext
  apply AlgHom.ext
  intro x
  apply (AddMonoidAlgebra.scalarTensorEquiv A (A ⧸ I ^ (n + 1)) (M := M)).injective
  change toGroupAlgebra ((pointEquiv C (AddMonoidAlgebra A M) (A ⧸ I ^ (n + 1)))
    ((baseChange (quotientMap I n)).map (lift I s))).1 x = groupPoint I s n x
  change toGroupAlgebra ((pointEquiv C (AddMonoidAlgebra A M) (A ⧸ I ^ (n + 1)))
    ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap A (A ⧸ I ^ (n + 1)))))).map
      ((hopfSpec (CommRingCat.of A)).map (CommHopfAlgCat.ofHom (algebraSystem I s).lift).op))).1 x =
        groupPoint I s n x
  rw [groupPoint_baseChange]
  exact (algebraSystem I s).reduce_lift (n + 1) x

/-- Surjectivity of the actual adic restriction map for standard diagonalizable Hopf spectra. -/
theorem restrict_surjective :
    Function.Surjective
      (Adic.System.restrict I (hopfGroup A (AddMonoidAlgebra A M)) (hopfGroup A C)) := by
  intro s
  refine ⟨lift I s, Adic.System.ext (fun n => lift_reduction I s n)⟩

/-- The actual coordinate bialgebra map of a homomorphism between Hopf spectra. -/
def coordinateMap (f : hopfGroup A (AddMonoidAlgebra A M) ⟶ hopfGroup A C) :
    C →ₐc[A] AddMonoidAlgebra A M :=
  (hopfSpec.fullyFaithful.preimage f).unop.hom

omit [IsNoetherianRing A] in
@[simp] theorem map_coordinateMap
    (f : hopfGroup A (AddMonoidAlgebra A M) ⟶ hopfGroup A C) :
    (hopfSpec (CommRingCat.of A)).map (CommHopfAlgCat.ofHom (coordinateMap f)).op = f :=
  hopfSpec.fullyFaithful.map_preimage f

omit [IsNoetherianRing A] in
/-- Adic restriction is injective on homomorphisms of these Hopf spectra. -/
theorem restrict_injective :
    Function.Injective
      (Adic.System.restrict I (hopfGroup A (AddMonoidAlgebra A M)) (hopfGroup A C)) := by
  intro f g hfg
  have hc : coordinateMap f = coordinateMap g := by
    apply BialgHom.ext
    intro x
    apply AddMonoidAlgebra.ext
    apply Finsupp.ext
    intro m
    apply congrFun (IsHausdorff.StrictMono.funext' I strictMono_add_one
      (f := fun _ : Unit => (coordinateMap f x).coeff m)
      (g := fun _ : Unit => (coordinateMap g x).coeff m) ?_) ()
    intro n _
    have hn := congrArg (fun s => s.hom n) hfg
    change (baseChange (quotientMap I n)).map f =
      (baseChange (quotientMap I n)).map g at hn
    rw [← map_coordinateMap f, ← map_coordinateMap g] at hn
    have hp := congrArg (fun u : RelativeHom (hopfGroup A (AddMonoidAlgebra A M))
        (hopfGroup A C) (specOver A (A ⧸ I ^ (n + 1))) =>
      toGroupAlgebra ((pointEquiv C (AddMonoidAlgebra A M) (A ⧸ I ^ (n + 1))) u).1) hn
    change toGroupAlgebra ((pointEquiv C (AddMonoidAlgebra A M) (A ⧸ I ^ (n + 1)))
      ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap A (A ⧸ I ^ (n + 1)))))).map
        ((hopfSpec (CommRingCat.of A)).map (CommHopfAlgCat.ofHom (coordinateMap f)).op))).1 =
      toGroupAlgebra ((pointEquiv C (AddMonoidAlgebra A M) (A ⧸ I ^ (n + 1)))
      ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap A (A ⧸ I ^ (n + 1)))))).map
        ((hopfSpec (CommRingCat.of A)).map (CommHopfAlgCat.ofHom (coordinateMap g)).op))).1 at hp
    rw [groupPoint_baseChange, groupPoint_baseChange] at hp
    simpa using congrArg (fun F : C →ₐ[A] AddMonoidAlgebra (A ⧸ I ^ (n + 1)) M =>
      (F x).coeff m) hp
  calc
    f = (hopfSpec (CommRingCat.of A)).map (CommHopfAlgCat.ofHom (coordinateMap f)).op :=
      (map_coordinateMap f).symm
    _ = (hopfSpec (CommRingCat.of A)).map (CommHopfAlgCat.ofHom (coordinateMap g)).op :=
      congrArg (fun k : C →ₐc[A] AddMonoidAlgebra A M =>
        (hopfSpec (CommRingCat.of A)).map (CommHopfAlgCat.ofHom k).op) hc
    _ = g := map_coordinateMap g

/-- The actual adic Hom comparison is bijective for standard diagonalizable Hopf spectra. -/
theorem restrict_bijective :
    Function.Bijective
      (Adic.System.restrict I (hopfGroup A (AddMonoidAlgebra A M)) (hopfGroup A C)) :=
  ⟨restrict_injective I, restrict_surjective I⟩

end Langlands.GroupScheme.HomScheme.AdicDiagonalizable

namespace Langlands.GroupScheme.HomScheme.Adic.System

variable {A : Type u} [CommRing A] (I : Ideal A)
variable {H G H' G' : GroupScheme (Spec (CommRingCat.of A))}

/-- Transport a formal homomorphism system along source and target isomorphisms. -/
def transport (eH : H' ≅ H) (eG : G ≅ G') (s : System I H G) : System I H' G' where
  hom n := HomScheme.transport eH eG (s.hom n)
  compatible n := by
    rw [evaluate_transport, s.compatible]

/-- Bijectivity of adic restriction is invariant under isomorphisms of both groups. -/
theorem restrict_bijective_of_iso (eH : H' ≅ H) (eG : G ≅ G')
    (h : Function.Bijective (restrict I H G)) :
    Function.Bijective (restrict I H' G') := by
  constructor
  · intro f g hfg
    have hfg0 : eH.inv ≫ f ≫ eG.inv = eH.inv ≫ g ≫ eG.inv := by
      apply h.1
      apply System.ext
      intro n
      have hn := congrArg (fun s : System I H' G' => s.hom n) hfg
      change (baseChange (Langlands.AlgebraicGeometry.AdicAffinePoints.quotientMap I n)).map f =
        (baseChange (Langlands.AlgebraicGeometry.AdicAffinePoints.quotientMap I n)).map g at hn
      simp only [restrict_hom, Functor.map_comp, hn]
    simpa using congrArg (fun f => eH.hom ≫ f ≫ eG.hom) hfg0
  · intro s
    obtain ⟨f, hf⟩ := h.2 (transport I eH.symm eG.symm s)
    refine ⟨eH.hom ≫ f ≫ eG.hom, System.ext (fun n => ?_)⟩
    have hn := congrArg (fun s : System I H G => s.hom n) hf
    change (baseChange (Langlands.AlgebraicGeometry.AdicAffinePoints.quotientMap I n)).map f =
      (baseChange (Langlands.AlgebraicGeometry.AdicAffinePoints.quotientMap I n)).map eH.inv ≫
        s.hom n ≫
          (baseChange (Langlands.AlgebraicGeometry.AdicAffinePoints.quotientMap I n)).map eG.inv at hn
    change (baseChange (Langlands.AlgebraicGeometry.AdicAffinePoints.quotientMap I n)).map
      (eH.hom ≫ f ≫ eG.hom) = s.hom n
    rw [Functor.map_comp, Functor.map_comp, hn]
    simp only [Category.assoc, ← Functor.map_comp_assoc, ← Functor.map_comp,
      eH.hom_inv_id, eG.inv_hom_id]
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
      Category.id_comp]
    exact CategoryTheory.Category.comp_id (s.hom n)

end Langlands.GroupScheme.HomScheme.Adic.System

namespace Langlands.GroupScheme.HomScheme.AdicDiagonalizable

open FiniteSource

variable {A : Type u} [CommRing A] [IsNoetherianRing A]
variable (I : Ideal A) [IsAdicComplete I A]

/-- The adic Hom comparison for every diagonalizable source and affine target. -/
theorem restrict_bijective_of_isDiagonalizable
    (H G : GroupScheme (Spec (CommRingCat.of A))) [IsAffineHom G.X.hom]
    (hH : RelativeMultiplicativeType.IsDiagonalizable H) :
    Function.Bijective (Adic.System.restrict I H G) := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨M, _, _, ⟨e⟩⟩ := hH
  let eH : hopfGroup A (AddMonoidAlgebra A M) ≅ H :=
    Diagonalizable.hopfSpecIso (CommRingCat.of A) M ≪≫
      Diagonalizable.relativeModelIso (CommRingCat.of A) M ≪≫ e.symm
  let eG : hopfGroup A (AffineCoordinates.hopfAlgebra G) ≅ G :=
    (hopfSpec (CommRingCat.of A)).mapIso
      (CommHopfAlgCat.ofIsoSelf (AffineCoordinates.hopfAlgebra G)).op ≪≫
        AffineCoordinates.hopfSpecIso G
  exact Adic.System.restrict_bijective_of_iso I eH.symm eG (restrict_bijective I)

end Langlands.GroupScheme.HomScheme.AdicDiagonalizable
