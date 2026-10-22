import Langlands.WeilDeligne.Basic
import Langlands.Weil.Representation.SumsTensor

/-! # Sums and tensor products of Weil–Deligne pairs -/

noncomputable section

universe uK uG uV uW uX uY

open CategoryTheory

namespace Langlands.WeilDeligneRepresentation

variable {K : Type uK} {G : Type uG} [Field K] [Group G] {ν : G →* Kˣ}

/-- The binary direct sum of pairs, with componentwise monodromy. -/
def sum (A : WeilDeligneRepresentation.{uK, uG, uV} K G ν)
    (B : WeilDeligneRepresentation.{uK, uG, uW} K G ν) :
    WeilDeligneRepresentation.{uK, uG, max uV uW} K G ν where
  toFiniteRepresentation := FiniteRepresentation.sum A.toFiniteRepresentation B.toFiniteRepresentation
  monodromy := A.monodromy.prodMap B.monodromy
  nilpotent := by
    obtain ⟨m, hm⟩ := A.nilpotent
    obtain ⟨n, hn⟩ := B.nilpotent
    have hp : IsNilpotent (A.monodromy, B.monodromy) := by
      refine ⟨m + n, ?_⟩
      apply Prod.ext <;> simp [pow_add, hm, hn]
    exact hp.map (LinearMap.prodMapRingHom K A B)
  covariance g := by
    change (A.representation g).prodMap (B.representation g) *
      A.monodromy.prodMap B.monodromy *
      (A.representation g⁻¹).prodMap (B.representation g⁻¹) = _
    rw [LinearMap.prodMap_mul, LinearMap.prodMap_mul, A.covariance, B.covariance,
      LinearMap.prodMap_smul]
    rfl

/-- The tensor product of pairs has monodromy `N ⊗ 1 + 1 ⊗ N'`. -/
def tensor (A : WeilDeligneRepresentation.{uK, uG, uV} K G ν)
    (B : WeilDeligneRepresentation.{uK, uG, uW} K G ν) :
    WeilDeligneRepresentation.{uK, uG, max uV uW} K G ν where
  toFiniteRepresentation :=
    FiniteRepresentation.tensor A.toFiniteRepresentation B.toFiniteRepresentation
  monodromy := TensorProduct.map A.monodromy 1 + TensorProduct.map 1 B.monodromy
  nilpotent := by
    have hcomm : Commute (TensorProduct.map A.monodromy (1 : Module.End K B))
        (TensorProduct.map (1 : Module.End K A) B.monodromy) := by
      show _ * _ = _ * _
      rw [← TensorProduct.map_mul, ← TensorProduct.map_mul]
      simp
    apply hcomm.isNilpotent_add
    · obtain ⟨m, hm⟩ := A.nilpotent
      exact ⟨m, by simp [TensorProduct.map_pow, hm]⟩
    · obtain ⟨n, hn⟩ := B.nilpotent
      exact ⟨n, by simp [TensorProduct.map_pow, hn]⟩
  covariance g := by
    change TensorProduct.map (A.representation g) (B.representation g) *
      (TensorProduct.map A.monodromy (1 : Module.End K B) +
        TensorProduct.map (1 : Module.End K A) B.monodromy) *
      TensorProduct.map (A.representation g⁻¹) (B.representation g⁻¹) =
        (ν g : K) • (TensorProduct.map A.monodromy (1 : Module.End K B) +
          TensorProduct.map (1 : Module.End K A) B.monodromy)
    rw [mul_add, add_mul]
    simp only [← TensorProduct.map_mul, mul_one]
    rw [A.covariance, B.covariance, ← map_mul, ← map_mul, mul_inv_cancel, map_one, map_one]
    rw [TensorProduct.map_smul_left, TensorProduct.map_smul_right, smul_add]

/-- Direct sum of morphisms of pairs. -/
def sumMap {A : WeilDeligneRepresentation.{uK, uG, uV} K G ν}
    {B : WeilDeligneRepresentation.{uK, uG, uW} K G ν}
    {C : WeilDeligneRepresentation.{uK, uG, uX} K G ν}
    {D : WeilDeligneRepresentation.{uK, uG, uY} K G ν}
    (f : Hom A C) (g : Hom B D) : Hom (sum A B) (sum C D) where
  intertwiner := FiniteRepresentation.sumMap f.intertwiner g.intertwiner
  comm_monodromy := by
    ext x
    exact Prod.ext (LinearMap.congr_fun f.comm_monodromy x.1)
      (LinearMap.congr_fun g.comm_monodromy x.2)

/-- Tensor product of morphisms of pairs. -/
def tensorMap {A : WeilDeligneRepresentation.{uK, uG, uV} K G ν}
    {B : WeilDeligneRepresentation.{uK, uG, uW} K G ν}
    {C : WeilDeligneRepresentation.{uK, uG, uX} K G ν}
    {D : WeilDeligneRepresentation.{uK, uG, uY} K G ν}
    (f : Hom A C) (g : Hom B D) : Hom (tensor A B) (tensor C D) where
  intertwiner := FiniteRepresentation.tensorMap f.intertwiner g.intertwiner
  comm_monodromy := by
    change TensorProduct.map f.intertwiner.toLinearMap g.intertwiner.toLinearMap ∘ₗ
        (TensorProduct.map A.monodromy 1 + TensorProduct.map 1 B.monodromy) =
      (TensorProduct.map C.monodromy 1 + TensorProduct.map 1 D.monodromy) ∘ₗ
        TensorProduct.map f.intertwiner.toLinearMap g.intertwiner.toLinearMap
    simp only [LinearMap.comp_add, LinearMap.add_comp, ← TensorProduct.map_comp,
      Module.End.one_eq_id, LinearMap.comp_id, LinearMap.id_comp]
    rw [f.comm_monodromy, g.comm_monodromy]

/-- Binary direct sum is a bifunctor on pairs. -/
def sumFunctor :
    (WeilDeligneRepresentation.{uK, uG, uV} K G ν ×
      WeilDeligneRepresentation.{uK, uG, uW} K G ν) ⥤
        WeilDeligneRepresentation.{uK, uG, max uV uW} K G ν where
  obj A := sum A.1 A.2
  map f := sumMap f.1 f.2
  map_id _ := by apply Hom.ext; ext x; rfl
  map_comp _ _ := by apply Hom.ext; ext x; rfl

/-- Tensor product is a bifunctor on pairs. -/
def tensorFunctor :
    (WeilDeligneRepresentation.{uK, uG, uV} K G ν ×
      WeilDeligneRepresentation.{uK, uG, uW} K G ν) ⥤
        WeilDeligneRepresentation.{uK, uG, max uV uW} K G ν where
  obj A := tensor A.1 A.2
  map f := tensorMap f.1 f.2
  map_id _ := by
    apply Hom.ext
    apply Representation.IntertwiningMap.ext
    apply TensorProduct.ext'
    intro x y
    rfl
  map_comp _ _ := by
    apply Hom.ext
    apply Representation.IntertwiningMap.ext
    apply TensorProduct.ext'
    intro x y
    rfl

/-- Sums preserve genuine pair equivalences. -/
def sumEquiv {A C : WeilDeligneRepresentation.{uK, uG, uV} K G ν}
    {B D : WeilDeligneRepresentation.{uK, uG, uW} K G ν} (e : Equiv A C) (f : Equiv B D) :
    Equiv (sum A B) (sum C D) :=
  Equiv.ofIso (sumFunctor.{uK, uG, uV, uW}.mapIso (e.toIso.prod f.toIso))

/-- Tensor products preserve genuine pair equivalences. -/
def tensorEquiv {A C : WeilDeligneRepresentation.{uK, uG, uV} K G ν}
    {B D : WeilDeligneRepresentation.{uK, uG, uW} K G ν} (e : Equiv A C) (f : Equiv B D) :
    Equiv (tensor A B) (tensor C D) :=
  Equiv.ofIso (tensorFunctor.{uK, uG, uV, uW}.mapIso (e.toIso.prod f.toIso))

/-- Binary sum on genuine pair classes. -/
def sumClass :
    IsomorphismClasses.{uK, uG, uV} K G ν → IsomorphismClasses.{uK, uG, uW} K G ν →
      IsomorphismClasses.{uK, uG, max uV uW} K G ν :=
  Quotient.map₂ sum (fun _ _ ⟨e⟩ _ _ ⟨f⟩ => ⟨sumEquiv e f⟩)

/-- Tensor product on genuine pair classes. -/
def tensorClass :
    IsomorphismClasses.{uK, uG, uV} K G ν → IsomorphismClasses.{uK, uG, uW} K G ν →
      IsomorphismClasses.{uK, uG, max uV uW} K G ν :=
  Quotient.map₂ tensor (fun _ _ ⟨e⟩ _ _ ⟨f⟩ => ⟨tensorEquiv e f⟩)

end Langlands.WeilDeligneRepresentation
