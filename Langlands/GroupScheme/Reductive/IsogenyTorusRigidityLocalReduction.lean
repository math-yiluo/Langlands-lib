import Langlands.GroupScheme.Reductive.TorusConjugationBaseChange
import Langlands.GroupScheme.Reductive.SuppliedToriSimultaneousSplitting
import Langlands.AbelianScheme.IsogenyStability

/-! # Reducing torus rigidity to split affine bases -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {G H : GroupScheme S} {T : CommGroupScheme S}

/-- Local conjugating covers for the canonical pullbacks along the members of
an fppf cover compose to a conjugating cover over the original base. -/
theorem fppfLocallyTorusConjugate_of_cover
    (i : T.toGrp ⟶ H) (f F : G ⟶ H)
    (𝒰 : Scheme.Cover.{u}
      (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)) S)
    (h : ∀ k : 𝒰.I₀, FppfLocallyTorusConjugate
      (T := (CommGroupScheme.baseChange (𝒰.f k)).obj T)
      ((GroupScheme.baseChange (𝒰.f k)).map i)
      ((GroupScheme.baseChange (𝒰.f k)).map f)
      ((GroupScheme.baseChange (𝒰.f k)).map F)) :
    FppfLocallyTorusConjugate i f F := by
  classical
  choose 𝒱 h𝒱 using h
  refine ⟨𝒰.bind 𝒱, fun k => ?_⟩
  obtain ⟨t, ht⟩ := h𝒱 k.1 k.2
  let V : Over (𝒰.X k.1) := Over.mk ((𝒱 k.1).f k.2)
  let a : Over.mk ((𝒰.bind 𝒱).f k) ⟶ (Over.map (𝒰.f k.1)).obj V :=
    Over.homMk (𝟙 _) (by simp only [Category.id_comp]; rfl)
  exact ⟨a ≫ baseChangePointsEquiv (𝒰.f k.1) T.toGrp V t,
    ((torusConjugates_baseChange_iff (𝒰.f k.1) i f F V t).mp ht).comp a⟩

/-- The remaining affine split existence assertion: isogenies with aligned
full split coordinates and the same torus restriction have local conjugators. -/
def SplitAffineIsogenyTorusConjugacyStatement : Prop :=
  ∀ (R : CommRingCat.{u})
    (G H : GroupScheme (Spec R)) (hG : IsReductive G) (hH : IsReductive H)
    (T U : CommGroupScheme (Spec R)) (i : T.toGrp ⟶ G) (j : U.toGrp ⟶ H),
    haveI := hG.isAffineHom
    haveI := hH.isAffineHom
    HasSplitMaximalTorusCoordinates i → HasSplitMaximalTorusCoordinates j →
    ∀ f F : G ⟶ H, IsIsogeny f → IsIsogeny F →
      (∃ τ : T.toGrp ⟶ U.toGrp, i ≫ f = τ ≫ j) → i ≫ f = i ≫ F →
      FppfLocallyTorusConjugate j f F

/-- Split affine local existence suffices for local conjugators over every
base scheme, for the two supplied maximal tori. -/
theorem fppfLocallyTorusConjugate_of_splitAffine
    (hlocal : SplitAffineIsogenyTorusConjugacyStatement.{u})
    (G H : GroupScheme S) (hG : IsReductive G) (hH : IsReductive H)
    (T U : CommGroupScheme S) (i : T.toGrp ⟶ G) (j : U.toGrp ⟶ H)
    (hT : RelativeTorus.IsTorus T.toGrp) (hi : IsClosedSubgroup i)
    (hmax : IsFibrewiseMaximalTorus i)
    (hU : RelativeTorus.IsTorus U.toGrp) (hj : IsClosedSubgroup j)
    (hmax' : IsFibrewiseMaximalTorus j)
    (f F : G ⟶ H) (hf : IsIsogeny f) (hF : IsIsogeny F)
    (hτ : ∃ τ : T.toGrp ⟶ U.toGrp, i ≫ f = τ ≫ j)
    (heq : i ≫ f = i ≫ F) :
    FppfLocallyTorusConjugate j f F := by
  classical
  let := hG.isAffineHom
  let := hH.isAffineHom
  have hsplit := commonEtaleLocalSplitCoordinates_of_suppliedTori
    G H hG hH T U i j hT hi hmax hU hj hmax'
  choose R b hb hpoint hsource htarget using hsplit
  let 𝒰 : Scheme.Cover.{u}
      (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)) S :=
    Scheme.Cover.mkOfCovers S (fun s => Spec (R s)) b
      (fun s => ⟨s, hpoint s⟩) (fun s => by
        let : Etale (b s) := hb s
        exact ⟨inferInstance, inferInstance⟩)
  apply fppfLocallyTorusConjugate_of_cover j f F 𝒰
  intro s
  apply hlocal (R s) ((GroupScheme.baseChange (b s)).obj G)
    ((GroupScheme.baseChange (b s)).obj H) (hG.baseChange (b s)) (hH.baseChange (b s))
    ((CommGroupScheme.baseChange (b s)).obj T)
    ((CommGroupScheme.baseChange (b s)).obj U)
    ((GroupScheme.baseChange (b s)).map i) ((GroupScheme.baseChange (b s)).map j)
    (hsource s) (htarget s)
    ((GroupScheme.baseChange (b s)).map f) ((GroupScheme.baseChange (b s)).map F)
    (hf.baseChange (b s)) (hF.baseChange (b s))
  · obtain ⟨τ, hτ⟩ := hτ
    exact ⟨(GroupScheme.baseChange (b s)).map τ, by
      simpa only [Functor.map_comp] using congrArg (GroupScheme.baseChange (b s)).map hτ⟩
  · simpa only [Functor.map_comp] using congrArg (GroupScheme.baseChange (b s)).map heq

/-- The unchanged general-base rigidity statement follows from the split
affine existence assertion; the reverse implication and uniqueness are already proved. -/
theorem reductiveIsogenyTorusRigidity_of_splitAffine
    (hlocal : SplitAffineIsogenyTorusConjugacyStatement.{u}) :
    ReductiveIsogenyTorusRigidityStatement.{u} := by
  intro S G' G hG' hG T' T i' i hT' hi' hmax' hT hi hmax f F hf hF hft hFT
  change (i' ≫ f = i' ≫ F ↔ FppfLocallyTorusConjugate i f F) ∧ _
  refine ⟨⟨fun heq => ?_, fun h => h.torusRestriction_eq hFT⟩, ?_⟩
  · exact fppfLocallyTorusConjugate_of_splitAffine hlocal
      G' G hG' hG T' T i' i hT' hi' hmax' hT hi hmax f F hf hF hft heq
  · intro V t₁ t₂ ht₁ ht₂ U a h
    have hc := TorusConjugates.difference_mem_center_of_isogeny hF ht₁ ht₂
    rw [mem_center] at hc
    simpa only [MonObj.comp_mul, GrpObj.comp_inv, Category.assoc] using (hc U a h).eq

end Langlands.GroupScheme
