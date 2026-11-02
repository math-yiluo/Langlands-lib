import Langlands.GroupScheme.Reductive.GeneralLinear
import Langlands.GroupScheme.RepresentedSubgroup
import Langlands.GroupScheme.Dynamic.ImproperParabolic

/-! # Reductivity transport for represented dynamic centralizers -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- A closed subgroup of an affine group scheme is affine over the base. -/
theorem IsClosedSubgroup.isAffineHom {S : Scheme.{u}} {M G : GroupScheme S} {j : M ⟶ G}
    (hj : IsClosedSubgroup j) [IsAffineHom G.X.hom] : IsAffineHom M.X.hom := by
  let : IsClosedImmersion j.hom.hom.left := hj
  rw [← Over.w j.hom.hom]
  infer_instance

/-- Connected reductivity is preserved by an isomorphism of group schemes. -/
theorem IsConnectedReductive.of_iso {k : Type u} [Field k]
    {G G' : GroupScheme (Spec (CommRingCat.of k))} (e : G ≅ G')
    (h : IsConnectedReductive G') : IsConnectedReductive G := by
  have hw : G.X.hom = e.hom.hom.hom.left ≫ G'.X.hom := (Over.w e.hom.hom.hom).symm
  have := isIso_left_of_iso e
  have := h.smooth
  have := h.isAffineHom
  have := h.connectedSpace
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hw]
    infer_instance
  · rw [hw]
    infer_instance
  · let φ := Scheme.homeoOfIso (asIso e.hom.hom.hom.left)
    exact φ.symm.surjective.connectedSpace φ.symm.continuous
  · exact HasTrivialUnipotentRadical.of_iso
      ((GroupScheme.baseChange (toAlgebraicClosure k)).mapIso e)
      h.hasTrivialGeometricUnipotentRadical

namespace SubgroupFunctor

/-- The identity group homomorphism represents the full subgroup functor. -/
theorem top_isRepresentedBy_id {S : Scheme.{u}} (G : GroupScheme S) :
    (⊤ : SubgroupFunctor G).IsRepresentedBy (𝟙 G) := by
  constructor
  · change Mono (𝟙 G.X)
    infer_instance
  · apply SubgroupFunctor.ext
    intro T
    apply Subgroup.ext
    intro x
    constructor
    · intro _
      exact Subgroup.mem_top _
    · intro _
      exact ⟨x, Category.comp_id x⟩

namespace IsRepresentedBy

/-- A representative of the full subgroup functor is isomorphic to the ambient group scheme. -/
def topIso {S : Scheme.{u}} {M G : GroupScheme S} {j : M ⟶ G}
    (hj : (⊤ : SubgroupFunctor G).IsRepresentedBy j) : M ≅ G :=
  hj.isoOfIsRepresentedBy (top_isRepresentedBy_id G)

theorem topIso_hom {S : Scheme.{u}} {M G : GroupScheme S} {j : M ⟶ G}
    (hj : (⊤ : SubgroupFunctor G).IsRepresentedBy j) : hj.topIso.hom = j := by
  have h := hj.isoOfIsRepresentedBy_hom_comp (top_isRepresentedBy_id G)
  simpa [topIso] using h

/-- Connected reductivity depends only on the represented subgroup functor. -/
theorem isConnectedReductive {k : Type u} [Field k]
    {G M N : GroupScheme (Spec (CommRingCat.of k))} {F : SubgroupFunctor G}
    {j : M ⟶ G} {i : N ⟶ G} (hj : F.IsRepresentedBy j) (hi : F.IsRepresentedBy i)
    (hN : IsConnectedReductive N) : IsConnectedReductive M :=
  hN.of_iso (hj.isoOfIsRepresentedBy hi)

end IsRepresentedBy
end SubgroupFunctor

namespace Dynamic

variable {k : Type u} [Field k] {G M : GroupScheme (Spec (CommRingCat.of k))}

/-- Every representative of a full dynamic centralizer is connected reductive if `G` is. -/
theorem isConnectedReductive_of_centralizer_eq_top (hG : IsConnectedReductive G)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) {j : M ⟶ G}
    (hj : (centralizer χ).IsRepresentedBy j) (hχ : centralizer χ = ⊤) :
    IsConnectedReductive M := by
  rw [hχ] at hj
  exact hG.of_iso hj.topIso

/-- The centralizer of the trivial cocharacter is reductive in every representative. -/
theorem isConnectedReductive_trivialCocharacter (hG : IsConnectedReductive G) {j : M ⟶ G}
    (hj : (centralizer (trivialCocharacter G)).IsRepresentedBy j) :
    IsConnectedReductive M :=
  isConnectedReductive_of_centralizer_eq_top hG _ hj (centralizer_trivialCocharacter G)

/-- Every dynamic-centralizer representative in a commutative connected reductive group
is connected reductive. -/
theorem isConnectedReductive_of_commutative
    (C : CommGroupScheme (Spec (CommRingCat.of k))) (hC : IsConnectedReductive C.toGrp)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ C.toGrp) {j : M ⟶ C.toGrp}
    (hj : (centralizer χ).IsRepresentedBy j) : IsConnectedReductive M :=
  isConnectedReductive_of_centralizer_eq_top hC χ hj (centralizer_eq_top_of_commutative C χ)

end Dynamic
end Langlands.GroupScheme
