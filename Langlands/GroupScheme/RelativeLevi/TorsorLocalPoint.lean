import Langlands.GroupScheme.RelativeLevi.ParabolicRadicalBaseChange
import Langlands.GroupScheme.Descent.AffineEtaleRefinement
import Langlands.AlgebraicGeometry.AlgebraicSpace.CoproductChart

/-! # An affine etale local point of the actual Levi presheaf -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Langlands.AlgebraicGeometry.AlgebraicSpace.CoproductChart

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.RelativeLevi

variable {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type (u + 1)}

private theorem subsingleton_sections_of_isEmpty
    (hF : Presieve.IsSheaf (Scheme.zariskiTopology.over S) F)
    (W : Over S) [IsEmpty W.left] : Subsingleton (F.obj (op W)) := by
  have hb : (⊥ : Sieve W) ∈ Scheme.zariskiTopology.over S W := by
    rw [GrothendieckTopology.mem_over_iff, (Sieve.overEquiv W).map_bot]
    exact W.left.bot_mem_grothendieckTopology
  let FS : Sheaf (Scheme.zariskiTopology.over S) (Type (u + 1)) :=
    ⟨F, (isSheaf_iff_isSheaf_of_type _ _).mpr hF⟩
  let := Types.isTerminalEquivUnique _ (FS.isTerminalOfBotCover W hb)
  infer_instance

private theorem nonempty_coproduct_sections
    (hF : Presieve.IsSheaf (Scheme.zariskiTopology.over S) F)
    {I : Type u} (V : I → Over S) (x : ∀ i, F.obj (op (V i))) :
    Nonempty (F.obj (op (sigmaOver V))) := by
  have hs : Presieve.IsSheafFor F (Presieve.ofArrows V (sigmaOverι V)) := by
    rw [Presieve.isSheafFor_iff_generate]
    apply hF
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
    exact (sigmaOpenCover (fun i => (V i).left)).mem_grothendieckTopology
  obtain ⟨y, _, _⟩ := (Presieve.isSheafFor_arrows_iff _ _).mp hs x (by
    intro i j W a b hab
    by_cases hij : i = j
    · subst j
      let : Mono (sigmaOverι V i) := Over.mono_of_mono_left _
      rw [(cancel_mono (sigmaOverι V i)).mp hab]
    · let : IsEmpty W.left := _root_.AlgebraicGeometry.isEmpty_of_commSq_sigmaι_of_ne
        (g := fun k => (V k).left)
        (show CommSq a.left b.left
          (Sigma.ι (fun k => (V k).left) i) (Sigma.ι (fun k => (V k).left) j) from
            ⟨congrArg (fun k => k.left) hab⟩) hij
      let := subsingleton_sections_of_isEmpty hF W
      exact Subsingleton.elim _ _)
  exact ⟨y⟩

/-- A section-bearing affine etale surjection over the original base. -/
structure AffineEtalePoint (F : (Over S)ᵒᵖ ⥤ Type (u + 1)) where
  test : Over S
  affine : IsAffine test.left
  etale : Etale test.hom
  surjective : Surjective test.hom
  point : F.obj (op test)

/-- Over an affine base, local sections on an etale cover give a section
on one affine etale surjection. -/
def affineEtalePointOfCover [IsAffine S]
    (hF : Presieve.IsSheaf (Scheme.zariskiTopology.over S) F)
    (𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S)
    (x : ∀ j, F.obj (op (Over.mk (𝒰.f j)))) : AffineEtalePoint F := by
  let V := fun j => Over.mk (𝒰.f j)
  let Q := sigmaOver V
  let : Etale Q.hom := IsZariskiLocalAtSource.sigmaDesc (P := @Etale) 𝒰.map_prop
  let : Surjective Q.hom := by
    change Surjective (Sigma.desc 𝒰.f)
    infer_instance
  let y := Classical.choice (nonempty_coproduct_sections hF V x)
  let R := Descent.affineEtaleRefinement Q.hom
  let W : Over S := Over.mk (R.map ≫ Q.hom)
  let a : W ⟶ Q := Over.homMk R.map
  exact ⟨W, R.affine, by
    change Etale (R.map ≫ Q.hom)
    infer_instance, R.surjective, F.map a.op y⟩

variable {G P : GroupScheme S} {i : P ⟶ G}

/-- A represented dynamic parabolic has an actual Levi subgroup image. -/
def dynamicLeviImage (hG : IsReductive G) (χ : (Gm S).toGrp ⟶ G)
    (hP : (Dynamic.parabolic χ).IsRepresentedBy i) : LeviImage P := by
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom G.X.hom := hG.isAffineHom
  choose U iU hUc hUlfp hU using (dynamicBaseRepresentability S G χ).2.1
  choose Z iZ hZc hZlfp hZ using (dynamicBaseRepresentability S G χ).2.2
  let l := Dynamic.centralizerToParabolic hP hZ
  exact LeviImage.ofHom l
    ((dynamicRelativeLevi S G P U Z χ i iU iZ hG hP hU hZ).2.2 l
      (Dynamic.centralizerToParabolic_comp hP hZ))

/-- A relative parabolic's actual Levi presheaf has an affine etale local
point over an affine base, once its Zariski sheaf condition is supplied. -/
def affineEtaleLeviPoint [IsAffine S]
    (hi : IsRelativeParabolicSubgroup i) (hG : IsReductive G)
    (hF : Presieve.IsSheaf (Scheme.zariskiTopology.over S)
      (moduliFunctorOfParabolic hi hG)) :
    AffineEtalePoint (moduliFunctorOfParabolic hi hG) := by
  choose 𝒰 h𝒰 using relativeParabolicEtaleLocalDynamic S G P i hG hi
  choose χ hχ using h𝒰
  exact affineEtalePointOfCover hF 𝒰
    (fun j => dynamicLeviImage (hG.baseChange (𝒰.f j)) (χ j) (hχ j))

end Langlands.GroupScheme.RelativeLevi
