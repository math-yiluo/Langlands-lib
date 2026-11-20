import Langlands.Geometry.FormalGroup.PolarizedFramedChangeFrame
import Langlands.Geometry.FormalGroup.HarrisSplitSpecialAffine

/-! # The action of rational polarized frame automorphisms -/

noncomputable section

universe u s w

namespace Langlands.FormalGroup.ModuleLaw.PolarizedOrderModule.RationalSimilitudeIso

open TopologicalSpace _root_.AlgebraicGeometry Langlands.Shimura

variable {prime : ℕ} [Fact prime.Prime]
variable {A : Type w} [Ring A] [Algebra ℤ_[prime] A] {star : AlgebraInvolution ℤ_[prime] A}
variable {R : Type} [CommRing R] [Algebra ℤ_[prime] R]

/-- Actual rational similitudes from a polarized order module to itself. -/
def Automorphism (X : PolarizedOrderModule A star R (prime : ℤ_[prime]))
    (U : Opens (PrimeSpectrum R)) :=
  RationalSimilitudeIso X X U

namespace Automorphism

variable {X : PolarizedOrderModule A star R (prime : ℤ_[prime])} {U : Opens (PrimeSpectrum R)}

/-- The stored rational similitude of an automorphism. -/
def toIso (g : Automorphism X U) : RationalSimilitudeIso X X U := g

instance : Group (Automorphism X U) where
  one := refl X U
  mul g h := h.toIso.trans g.toIso
  inv g := g.toIso.symm
  one_mul g := ext (RationalSection.id_comp g.toIso.sectionIso.hom)
  mul_one g := ext (RationalSection.comp_id g.toIso.sectionIso.hom)
  mul_assoc g h k := ext (RationalSection.comp_assoc g.toIso.sectionIso.hom
    h.toIso.sectionIso.hom k.toIso.sectionIso.hom)
  inv_mul_cancel g := ext g.toIso.sectionIso.inv_hom

@[simp]
theorem toIso_one : (1 : Automorphism X U).toIso = refl X U := rfl

@[simp]
theorem toIso_mul (g h : Automorphism X U) : (g * h).toIso = h.toIso.trans g.toIso := rfl

@[simp]
theorem toIso_inv (g : Automorphism X U) : g⁻¹.toIso = g.toIso.symm := rfl

end Automorphism

end Langlands.FormalGroup.ModuleLaw.PolarizedOrderModule.RationalSimilitudeIso

namespace Langlands.FormalGroup.PolarizedFramedAffinePoint

open CategoryTheory ModuleLaw Langlands.Shimura

variable {prime : ℕ} [Fact prime.Prime]
variable {W : Type} [CommRing W] [Algebra ℤ_[prime] W] {π : W}
variable {A : Type w} [Ring A] [Algebra ℤ_[prime] A] {star : AlgebraInvolution ℤ_[prime] A}
variable {frame : PolarizedOrderModule A star (ResidueRing W π) (prime : ℤ_[prime])}
variable {T U : Nilp.{0, 0} W π}

instance : MulAction (PolarizedOrderModule.RationalSimilitudeIso.Automorphism frame ⊤)
    (IsomorphismClass (frame := frame) (T := T)) where
  smul g q := q.changeFrame g.toIso
  one_smul q := q.changeFrame_refl
  mul_smul g h q := (q.changeFrame_trans h.toIso g.toIso).symm

theorem IsomorphismClass.smul_eq_changeFrame
    (g : PolarizedOrderModule.RationalSimilitudeIso.Automorphism frame ⊤)
    (q : IsomorphismClass (frame := frame) (T := T)) :
    g • q = q.changeFrame g.toIso := rfl

/-- Coefficient maps commute with the action by inverse precomposition. -/
theorem IsomorphismClass.smul_baseChange
    (g : PolarizedOrderModule.RationalSimilitudeIso.Automorphism frame ⊤)
    (q : IsomorphismClass (frame := frame) (T := T)) (j : T ⟶ U) :
    (g • q).baseChange j = g • q.baseChange j :=
  q.changeFrame_baseChange g.toIso j

/-- The fixed polarized residue frame acts by natural automorphisms of the affine functor. -/
def frameActionHom (frame : PolarizedOrderModule A star (ResidueRing W π) (prime : ℤ_[prime])) :
    PolarizedOrderModule.RationalSimilitudeIso.Automorphism frame ⊤ →*
      Aut (classFunctor frame) where
  toFun g := changeFrameNatIso g.toIso
  map_one' := by
    apply Aut.ext
    ext T q
    exact q.changeFrame_refl
  map_mul' g h := by
    apply Aut.ext
    ext T q
    exact (q.changeFrame_trans h.toIso g.toIso).symm

@[simp]
theorem frameActionHom_hom_app
    (g : PolarizedOrderModule.RationalSimilitudeIso.Automorphism frame ⊤)
    (q : IsomorphismClass (frame := frame) (T := T)) :
    (frameActionHom frame g).hom.app T q = g • q := rfl

end Langlands.FormalGroup.PolarizedFramedAffinePoint

namespace Langlands.FormalGroup.Harris

open CategoryTheory ValuativeRel LocalDivision ModuleLaw Langlands.Shimura

attribute [local instance] ModuleLaw.coefficientAlgebra ModuleLaw.coefficientScalarTower
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

variable {prime : ℕ} [Fact prime.Prime]
variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable [Algebra ℤ_[prime] 𝒪[K]]
variable {W : Type} [CommRing W] [Algebra 𝒪[K] W] [Algebra ℤ_[prime] W]
variable [wTower : IsScalarTower ℤ_[prime] 𝒪[K] W] {ϖ : 𝒪[K]}
variable {L : Type s} [Field L] [Algebra K L] (ι : L →ₐ[K] D)
variable {frame frame' : SplitPolarizedFrame prime K D W ϖ}
variable {T : Nilp.{0, 0} W (algebraMap 𝒪[K] W ϖ)}

local instance : Algebra ℤ_[prime] (IntegerRing K D) :=
  Algebra.compHom (IntegerRing K D) (algebraMap ℤ_[prime] 𝒪[K])

omit wTower in
/-- The target tangent condition is invariant under actual change of the residue frame. -/
theorem isSplitSpecialClass_changeFrame_iff
    (e : PolarizedOrderModule.RationalSimilitudeIso frame frame' ⊤)
    (q : PolarizedFramedAffinePoint.IsomorphismClass (frame := frame) (T := T)) :
    isSplitSpecialClass ι (q.changeFrame e) ↔ isSplitSpecialClass ι q := by
  induction q using Quotient.inductionOn with
  | h X => rfl

instance : MulAction (PolarizedOrderModule.RationalSimilitudeIso.Automorphism frame ⊤)
    ((splitSpecialAffineFunctor ι frame).obj T) where
  smul g q := ⟨g • q.val, (isSplitSpecialClass_changeFrame_iff ι g.toIso q.val).2 q.property⟩
  one_smul q := Subtype.ext (one_smul _ q.val)
  mul_smul g h q := Subtype.ext (mul_smul g h q.val)

/-- Change of frame restricts to a natural isomorphism on the actual split-special loci. -/
def splitSpecialChangeFrameNatIso
    (e : PolarizedOrderModule.RationalSimilitudeIso frame frame' ⊤) :
    splitSpecialAffineFunctor ι frame ≅ splitSpecialAffineFunctor ι frame' where
  hom := {
    app _ := ↾(fun q => ⟨q.val.changeFrame e, (isSplitSpecialClass_changeFrame_iff ι e q.val).2 q.property⟩)
    naturality _ _ j := by
      ext q
      apply Subtype.ext
      exact (q.val.changeFrame_baseChange e j).symm }
  inv := {
    app _ := ↾(fun q => ⟨q.val.changeFrame e.symm,
      (isSplitSpecialClass_changeFrame_iff ι e.symm q.val).2 q.property⟩)
    naturality _ _ j := by
      ext q
      apply Subtype.ext
      exact (q.val.changeFrame_baseChange e.symm j).symm }
  hom_inv_id := by
    ext T q
    apply Subtype.ext
    exact ConcreteCategory.congr_hom (NatTrans.congr_app
      (PolarizedFramedAffinePoint.changeFrameNatIso e).hom_inv_id T) q.val
  inv_hom_id := by
    ext T q
    apply Subtype.ext
    exact ConcreteCategory.congr_hom (NatTrans.congr_app
      (PolarizedFramedAffinePoint.changeFrameNatIso e).inv_hom_id T) q.val

/-- Rational similitudes of one fixed frame act on the split-special affine functor. -/
def splitSpecialFrameActionHom (frame : SplitPolarizedFrame prime K D W ϖ) :
    PolarizedOrderModule.RationalSimilitudeIso.Automorphism frame ⊤ →*
      Aut (splitSpecialAffineFunctor ι frame) where
  toFun g := splitSpecialChangeFrameNatIso ι g.toIso
  map_one' := by
    apply Aut.ext
    ext T q
    apply Subtype.ext
    exact q.val.changeFrame_refl
  map_mul' g h := by
    apply Aut.ext
    ext T q
    apply Subtype.ext
    exact (q.val.changeFrame_trans h.toIso g.toIso).symm

omit wTower in
@[simp]
theorem splitSpecialFrameActionHom_hom_app
    (g : PolarizedOrderModule.RationalSimilitudeIso.Automorphism frame ⊤)
    (q : (splitSpecialAffineFunctor ι frame).obj T) :
    (splitSpecialFrameActionHom ι frame g).hom.app T q = g • q := rfl

omit wTower in
/-- The inclusion of the split-special locus intertwines the two natural actions. -/
theorem splitSpecialFrameActionHom_inclusion
    (g : PolarizedOrderModule.RationalSimilitudeIso.Automorphism frame ⊤) :
    (splitSpecialFrameActionHom ι frame g).hom ≫ splitSpecialToPolarized ι frame =
      splitSpecialToPolarized ι frame ≫ (PolarizedFramedAffinePoint.frameActionHom frame g).hom :=
  rfl

end Langlands.FormalGroup.Harris
