import Langlands.GroupScheme.Torus.MultiplicativeType
import Langlands.GroupScheme.Torus.BaseChange
import Langlands.GroupScheme.Torus.DiagonalizableBaseChange

/-! # A common splitting field for two groups of multiplicative type -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]

/-- Two group schemes over `k` have a common splitting field: over a single field
extension `K / k` both become diagonalizable with finitely generated character groups. -/
def IsMultiplicativeType.HasCommonSplitting
    (Q N : GroupScheme (Spec (CommRingCat.of k))) : Prop :=
  ∃ (K : Type u) (_ : Field K) (_ : Algebra k K) (Λ Λ' : Type u) (_ : AddCommGroup Λ)
    (_ : AddCommGroup Λ') (_ : AddGroup.FG Λ) (_ : AddGroup.FG Λ'),
    Nonempty (((GroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj Q) ≅
        (Diagonalizable.groupScheme (CommRingCat.of K) Λ).toGrp) ∧
    Nonempty (((GroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj N) ≅
        (Diagonalizable.groupScheme (CommRingCat.of K) Λ').toGrp)

namespace IsMultiplicativeType

/-- A diagonalizable splitting over `Spec R` survives a further base change `c`. -/
private theorem nonempty_iso_baseChange_comp {S : Scheme.{u}} {R R' : CommRingCat.{u}}
    (b : Spec R ⟶ S) (c : Spec R' ⟶ Spec R) (G : GroupScheme S)
    (Λ : Type u) [AddCommGroup Λ]
    (e : (GroupScheme.baseChange b).obj G ≅ (Diagonalizable.groupScheme R Λ).toGrp) :
    Nonempty ((GroupScheme.baseChange (c ≫ b)).obj G ≅
      (Diagonalizable.groupScheme R' Λ).toGrp) :=
  ⟨(Functor.mapGrpNatIso (Over.pullbackComp c b)).app G ≪≫
    Functor.mapGrpCompIso.app G ≪≫ (GroupScheme.baseChange c).mapIso e ≪≫
      Diagonalizable.baseChangeIso c Λ⟩

/-- Ring-level form: a splitting over `K` survives every field map `K →+* E` compatible
with the structure maps from `k`. -/
private theorem nonempty_iso_of_ringHom {K E : Type u} [Field K] [Field E]
    [Algebra k K] [Algebra k E] (f : K →+* E)
    (hf : f.comp (algebraMap k K) = algebraMap k E)
    (G : GroupScheme (Spec (CommRingCat.of k))) (Λ : Type u) [AddCommGroup Λ]
    (e : (GroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G ≅
        (Diagonalizable.groupScheme (CommRingCat.of K) Λ).toGrp) :
    Nonempty ((GroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap k E)))).obj G ≅
        (Diagonalizable.groupScheme (CommRingCat.of E) Λ).toGrp) := by
  have h : Spec.map (CommRingCat.ofHom (algebraMap k E)) =
      Spec.map (CommRingCat.ofHom f) ≫ Spec.map (CommRingCat.ofHom (algebraMap k K)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hf]
  rw [h]
  exact nonempty_iso_baseChange_comp _ _ G Λ e

/-- Two finite-type groups of multiplicative type over a field split over a common
field extension. -/
theorem exists_common_splitting {Q N : GroupScheme (Spec (CommRingCat.of k))}
    (hQ : IsMultiplicativeType Q) (hN : IsMultiplicativeType N) :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra k K) (Λ Λ' : Type u) (_ : AddCommGroup Λ)
      (_ : AddCommGroup Λ') (_ : AddGroup.FG Λ) (_ : AddGroup.FG Λ'),
      Nonempty (((GroupScheme.baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj Q) ≅
          (Diagonalizable.groupScheme (CommRingCat.of K) Λ).toGrp) ∧
      Nonempty (((GroupScheme.baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj N) ≅
          (Diagonalizable.groupScheme (CommRingCat.of K) Λ').toGrp) := by
  obtain ⟨K₁, hK₁, a₁, Λ, hΛ, hΛfg, ⟨e₁⟩⟩ := hQ
  obtain ⟨K₂, hK₂, a₂, Λ', hΛ', hΛ'fg, ⟨e₂⟩⟩ := hN
  let E := TorusBaseChange.commonExtension k K₁ K₂
  let : Field E.carrier := E.field
  let : Algebra k E.carrier := (E.leftHom.comp (algebraMap k K₁)).toAlgebra
  exact ⟨E.carrier, inferInstance, inferInstance, Λ, Λ', hΛ, hΛ', hΛfg, hΛ'fg,
    nonempty_iso_of_ringHom E.leftHom rfl Q Λ e₁,
    nonempty_iso_of_ringHom E.rightHom E.compatible.symm N Λ' e₂⟩

/-- The common-splitting property of two groups of multiplicative type. -/
theorem hasCommonSplitting {Q N : GroupScheme (Spec (CommRingCat.of k))}
    (hQ : IsMultiplicativeType Q) (hN : IsMultiplicativeType N) :
    HasCommonSplitting Q N :=
  exists_common_splitting hQ hN

end IsMultiplicativeType

end Langlands.GroupScheme
