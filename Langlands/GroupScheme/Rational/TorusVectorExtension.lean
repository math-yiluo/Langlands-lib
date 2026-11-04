import Langlands.GroupScheme.Rational.SplitTorusVectorExtension
import Langlands.GroupScheme.Rational.VectorExtensionDescent
import Langlands.GroupScheme.Dynamic.ActionConjugation

/-! # Group sections of arbitrary-torus extensions by linear vector groups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

namespace splitTorus

variable {k : Type u} [Field k] (K : Type u) [Field K] [Algebra k K]
    {E V : GroupScheme (Spec (CommRingCat.of k))}
    (n : V ⟶ E) [Mono n.hom.hom]

local notation "b" => algebraBaseMap k K

local instance : Mono ((GroupScheme.baseChange b).map n).hom.hom :=
  Functor.map_mono (Over.pullback b) n.hom.hom

/-- Actual conjugation on a normal subgroup commutes with base change. -/
theorem conj_baseChange
    (hn : (SubgroupFunctor.range n).IsNormalizedBy (SubgroupFunctor.range (𝟙 E)))
    (hn' : (SubgroupFunctor.range ((GroupScheme.baseChange b).map n)).IsNormalizedBy
      (SubgroupFunctor.range (𝟙 ((GroupScheme.baseChange b).obj E)))) :
    (conj n hn).baseChange b = conj ((GroupScheme.baseChange b).map n) hn' := by
  apply AutomorphicAction.ext_act
  intro T g v
  apply (GroupScheme.baseChangePointsEquiv b V T).injective
  apply (cancel_mono n.hom.hom).1
  rw [AutomorphicAction.baseChangePointsEquiv_act, conj_act_comp,
    ← GroupScheme.baseChangePointsEquiv_comp b n T
      ((conj ((GroupScheme.baseChange b).map n) hn').act g v),
    conj_act_comp, map_mul, map_mul, map_inv,
    GroupScheme.baseChangePointsEquiv_comp]

end splitTorus

open RelativeRoot

variable {k : Type u} [Field k]
    {E V H : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom V.X.hom] [IsAffineHom H.X.hom]
    (n : V ⟶ E) [Mono n.hom.hom] (q : E ⟶ H)
    (hn : SubgroupFunctor.range n = SubgroupFunctor.range (kernelι q))
    (s : H.X ⟶ E.X) (hs : s ≫ q.hom.hom = 𝟙 H.X) {d : ℕ}
    (e : ∀ T : Over (Spec (CommRingCat.of k)),
      (T ⟶ V.X) ≃* Multiplicative (Fin d → Γ(T.left, ⊤)))
    (he : IsLinearVectorCoordinates (VectorExtensionDescent.action n q hn) e)

include hs he in
/-- An extension of an arbitrary torus by a linear vector group splits once it
has a section as a morphism of schemes. -/
theorem IsTorus.exists_extensionSection (hH : IsTorus H) :
    ∃ σ : H ⟶ E, σ ≫ q = 𝟙 H := by
  classical
  obtain ⟨K, _, _, hHK⟩ := hH
  let b := algebraBaseMap k K
  let nK := (GroupScheme.baseChange b).map n
  let qK := (GroupScheme.baseChange b).map q
  let : Mono nK.hom.hom := Functor.map_mono (Over.pullback b) n.hom.hom
  let : IsAffineHom ((GroupScheme.baseChange b).obj V).X.hom := by
    change IsAffineHom (CategoryTheory.Limits.pullback.snd V.X.hom b)
    infer_instance
  have hnK : SubgroupFunctor.range nK = SubgroupFunctor.range (kernelι qK) :=
    VectorExtensionDescent.range_baseChange_kernel n q hn K
  have hnK' : (SubgroupFunctor.range nK).IsNormalizedBy
      (SubgroupFunctor.range (𝟙 ((GroupScheme.baseChange b).obj E))) :=
    QuotientHomCocycle.normalized nK qK hnK (𝟙 _)
  have haction : (VectorExtensionDescent.action n q hn).baseChange b =
      splitTorus.conj nK hnK' :=
    splitTorus.conj_baseChange K n (QuotientHomCocycle.normalized n q hn (𝟙 E)) hnK'
  have heK : IsLinearVectorCoordinates (splitTorus.conj nK hnK')
      (vectorBaseChangeCoordinates e K) := by
    rw [← haction]
    exact he.baseChange
  have hkerK : ∀ (T : Over (Spec (CommRingCat.of K)))
      (g : T ⟶ ((GroupScheme.baseChange b).obj E).X),
      g ∈ (SubgroupFunctor.range nK).carrier T ↔ g ≫ qK.hom.hom = 1 := by
    intro T g
    rw [hnK, mem_range_kernelι_iff]
  have hsK : VectorExtensionDescent.baseChangedSection s K ≫ qK.hom.hom = 𝟙 _ := by
    change (Over.pullback b).map s ≫ (Over.pullback b).map q.hom.hom = 𝟙 _
    rw [← Functor.map_comp, hs, CategoryTheory.Functor.map_id]
  obtain ⟨σK, hσK⟩ := hHK.exists_extensionSection nK hnK' qK hkerK
    (VectorExtensionDescent.baseChangedSection s K) hsK (vectorBaseChangeCoordinates e K) heK
  exact ⟨VectorExtensionDescent.extensionSectionOfBaseChange n q hn s hs e he K σK hσK,
    VectorExtensionDescent.extensionSectionOfBaseChange_comp n q hn s hs e he K σK hσK⟩

/-- A chosen homomorphic section of an arbitrary-torus extension by a linear
vector group, constructed from a supplied scheme section. -/
def IsTorus.extensionSection (hH : IsTorus H) : H ⟶ E :=
  Classical.choose (hH.exists_extensionSection n q hn s hs e he)

/-- The chosen homomorphic section splits the original quotient map. -/
theorem IsTorus.extensionSection_comp (hH : IsTorus H) :
    hH.extensionSection n q hn s hs e he ≫ q = 𝟙 H :=
  Classical.choose_spec (hH.exists_extensionSection n q hn s hs e he)

end Langlands.GroupScheme
