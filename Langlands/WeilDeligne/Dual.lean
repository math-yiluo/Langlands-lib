import Langlands.WeilDeligne.Basic
import Langlands.Weil.Representation.Dual

/-! # Dual Weil–Deligne pairs with negative-transpose monodromy -/

noncomputable section

universe uK uG uV uW

open CategoryTheory Opposite

namespace Langlands.WeilDeligneRepresentation

variable {K : Type uK} {G : Type uG} [Field K] [Group G] {ν : G →* Kˣ}

private theorem dualMap_pow {V : Type uV} [AddCommGroup V] [Module K V]
    (f : Module.End K V) (n : ℕ) : (f ^ n).dualMap = f.dualMap ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', pow_succ, ← ih]
    rfl

/-- The dual pair has inverse-element dual action and monodromy `-transpose N`. -/
def dual (A : WeilDeligneRepresentation.{uK, uG, uV} K G ν) :
    WeilDeligneRepresentation.{uK, uG, max uK uV} K G ν where
  toFiniteRepresentation := FiniteRepresentation.dual A.toFiniteRepresentation
  monodromy := -A.monodromy.dualMap
  nilpotent := by
    change IsNilpotent (-A.monodromy.dualMap : Module.End K (Module.Dual K A))
    apply IsNilpotent.neg (R := Module.End K (Module.Dual K A))
    obtain ⟨n, hn⟩ := A.nilpotent
    refine ⟨n, ?_⟩
    rw [← dualMap_pow, hn]
    ext ℓ v
    exact map_zero ℓ
  covariance g := by
    change A.representation.dual g * (-A.monodromy.dualMap) *
      A.representation.dual g⁻¹ = (ν g : K) • (-A.monodromy.dualMap)
    ext ℓ v
    change -ℓ (A.representation (g⁻¹)⁻¹
      (A.monodromy (A.representation g⁻¹ v))) = (ν g : K) * -ℓ (A.monodromy v)
    rw [inv_inv]
    have h := LinearMap.congr_fun (A.covariance g) v
    change A.representation g (A.monodromy (A.representation g⁻¹ v)) =
      (ν g : K) • A.monodromy v at h
    rw [h, map_smul]
    simp

/-- A morphism of pairs induces the reverse morphism of dual pairs. -/
def dualMap {A : WeilDeligneRepresentation.{uK, uG, uV} K G ν}
    {B : WeilDeligneRepresentation.{uK, uG, uW} K G ν} (f : Hom A B) :
    Hom (dual B) (dual A) where
  intertwiner := Langlands.dualIntertwining f.intertwiner
  comm_monodromy := by
    change f.intertwiner.toLinearMap.dualMap ∘ₗ (-B.monodromy.dualMap) =
      (-A.monodromy.dualMap) ∘ₗ f.intertwiner.toLinearMap.dualMap
    ext ℓ v
    change -ℓ (B.monodromy (f.intertwiner v)) =
      -ℓ (f.intertwiner (A.monodromy v))
    exact congrArg (fun y => -ℓ y) (LinearMap.congr_fun f.comm_monodromy v).symm

/-- The contravariant dual functor on pairs. -/
def dualFunctor : (WeilDeligneRepresentation.{uK, uG, uV} K G ν)ᵒᵖ ⥤
    WeilDeligneRepresentation.{uK, uG, max uK uV} K G ν where
  obj A := dual A.unop
  map f := dualMap f.unop
  map_id _ := by apply Hom.ext; ext ℓ; rfl
  map_comp _ _ := by apply Hom.ext; ext ℓ; rfl

/-- Genuine pair equivalences induce reverse dual equivalences. -/
def dualEquiv {A : WeilDeligneRepresentation.{uK, uG, uV} K G ν}
    {B : WeilDeligneRepresentation.{uK, uG, uW} K G ν} (e : Equiv A B) :
    Equiv (dual B) (dual A) where
  representationEquiv := Langlands.dualEquiv e.representationEquiv
  comm_monodromy := (dualMap e.toHom).comm_monodromy

/-- Negative-transpose duality descends to genuine pair isomorphism classes. -/
def dualClass : IsomorphismClasses.{uK, uG, uV} K G ν →
    IsomorphismClasses.{uK, uG, max uK uV} K G ν :=
  Quotient.map dual (fun _ _ ⟨e⟩ => ⟨(dualEquiv e).symm⟩)

end Langlands.WeilDeligneRepresentation
