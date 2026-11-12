import Langlands.Geometry.Building.CrossTorusCentralizerCompatibility
import Langlands.GroupScheme.Torus.MaximalBaseChangeForwardReduction
import Langlands.GroupScheme.Torus.LatticeGalois

/-!
# Base change of the actual centralizer datum

The restriction-evaluation bijectivity of a centralizer datum transfers along a based
isomorphism to any representative of the full torus centralizer. Consequently the base change
of a centralizer datum along a field extension is again a centralizer datum, as soon as the
base-changed torus is isomorphic, compatibly with an isomorphism of ambient groups, to a torus
carrying a centralizer datum.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building

namespace CentralizerDatum

section Bijective

variable {K : Type u} [Field K]
  {S S' : CommGroupScheme (Spec (CommRingCat.of K))}
  {G H Z : GroupScheme (Spec (CommRingCat.of K))}
  {i : S.toGrp ⟶ G} {j : S'.toGrp ⟶ H}

/-- Bijectivity of restriction evaluation transfers along a based isomorphism `(e, f)` from a
centralizer datum `E` of `j` to any representative `l` of the full centralizer of `i` through
which `i` factors. -/
theorem bijective_restrictionEvaluation_of_basedIso (E : CentralizerDatum j)
    (e : S ≅ S') (f : G ≅ H) (h : i ≫ f.hom = CommGroupScheme.groupHom e.hom ≫ j)
    {l : Z ⟶ G} {s : S.toGrp ⟶ Z} (hl : (torusCentralizer i).IsRepresentedBy l)
    (hs : s ≫ l = i) :
    Function.Bijective (BruhatTits.Cartan.restrictionEvaluation s) := by
  let eGrp : S.toGrp ≅ S'.toGrp :=
    { hom := CommGroupScheme.groupHom e.hom
      inv := CommGroupScheme.groupHom e.inv
      hom_inv_id := congrArg CommGroupScheme.groupHom e.hom_inv_id
      inv_hom_id := congrArg CommGroupScheme.groupHom e.inv_hom_id }
  let ψ : Z ≅ E.Z :=
    (hl.torusCentralizer_of_iso_square eGrp f h).isoOfIsRepresentedBy E.isRepresentedBy
  have hψ : ψ.hom ≫ E.j = l ≫ f.hom :=
    SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp _ E.isRepresentedBy
  have htorus : s ≫ ψ.hom = CommGroupScheme.groupHom e.hom ≫ E.s := by
    apply E.isRepresentedBy.hom_ext
    rw [Category.assoc, hψ, ← Category.assoc, hs, Category.assoc, E.comp_eq, h]
  have hchar : ∀ chi : rationalCharacters E.Z,
      characterLattice.congr e
          (BruhatTits.Cartan.characterRestriction s (characterRestrict ψ.hom chi)) =
        BruhatTits.Cartan.characterRestriction E.s chi := by
    intro chi
    change CommGroupScheme.groupHom e.inv ≫ (s ≫ ψ.hom) ≫ chi.toMul = E.s ≫ chi.toMul
    rw [htorus]
    change CommGroupScheme.groupHom (e.inv ≫ e.hom) ≫ E.s ≫ chi.toMul = _
    rw [Iso.inv_hom_id]
    rfl
  have hkey : ∀ v : V S,
      (BruhatTits.Cartan.restrictionEvaluation s v).comp (characterRestrict ψ.hom) =
        BruhatTits.Cartan.restrictionEvaluation E.s (cocharacterRealCongr e v) := by
    intro v
    apply AddMonoidHom.ext
    intro chi
    rw [AddMonoidHom.comp_apply, BruhatTits.Cartan.restrictionEvaluation_apply,
      BruhatTits.Cartan.restrictionEvaluation_apply, ← hchar chi, eval_cocharacterRealCongr]
  have hsurj : Function.Surjective (characterRestrict ψ.hom) := by
    intro chi
    refine ⟨characterRestrict ψ.inv chi, ?_⟩
    rw [← AddMonoidHom.comp_apply, ← characterRestrict_comp, Iso.hom_inv_id, characterRestrict_id]
    rfl
  have hinj : ∀ φ φ' : rationalCharacters Z →+ ℝ,
      φ.comp (characterRestrict ψ.hom) = φ'.comp (characterRestrict ψ.hom) → φ = φ' := by
    intro φ φ' hφ
    apply AddMonoidHom.ext
    intro chi
    obtain ⟨chi', rfl⟩ := hsurj chi
    exact DFunLike.congr_fun hφ chi'
  constructor
  · intro v w hvw
    apply (cocharacterRealCongr e).injective
    apply E.bijective.1
    rw [← hkey, ← hkey, hvw]
  · intro φ
    obtain ⟨u, hu⟩ := E.bijective.2 (φ.comp (characterRestrict ψ.hom))
    refine ⟨(cocharacterRealCongr e).symm u, hinj _ _ ?_⟩
    rw [hkey, LinearEquiv.apply_symm_apply, hu]

end Bijective

section BaseChange

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {i : S.toGrp ⟶ G} (C : CentralizerDatum i)

local notation "b" => algebraBaseMap k K
local notation "S_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) S
local notation "G_K" => CategoryTheory.Functor.obj (GroupScheme.baseChange b) G
local notation "i_K" => CategoryTheory.Functor.map (GroupScheme.baseChange b) i

/-- The base change of the centralizer inclusion represents the full centralizer of the
base-changed torus. -/
theorem isRepresentedBy_baseChange :
    (torusCentralizer (T := S_K) i_K).IsRepresentedBy
      ((GroupScheme.baseChange b).map C.j) := by
  rw [torusCentralizer_baseChange]
  exact C.isRepresentedBy.baseChange b

/-- The base-changed torus factors through the base-changed centralizer. -/
theorem comp_eq_baseChange :
    (GroupScheme.baseChange b).map C.s ≫ (GroupScheme.baseChange b).map C.j = i_K := by
  rw [← Functor.map_comp, C.comp_eq]

variable {S' : CommGroupScheme (Spec (CommRingCat.of K))}
  {H : GroupScheme (Spec (CommRingCat.of K))} {j : S'.toGrp ⟶ H}
  (E : CentralizerDatum j)

/-- The base change of a centralizer datum along `k → K`, given a based isomorphism of the
base-changed torus and group to a torus and group carrying a centralizer datum `E`: its group,
inclusion and torus factorization are the actual base changes of those of `C`. -/
def baseChangeOfBasedIso (e : S_K ≅ S') (f : G_K ≅ H)
    (h : i_K ≫ f.hom = CommGroupScheme.groupHom e.hom ≫ j) :
    CentralizerDatum (S := S_K) i_K where
  Z := (GroupScheme.baseChange b).obj C.Z
  j := (GroupScheme.baseChange b).map C.j
  s := (GroupScheme.baseChange b).map C.s
  isClosedSubgroup := C.isClosedSubgroup.baseChange b
  isRepresentedBy := C.isRepresentedBy_baseChange
  comp_eq := C.comp_eq_baseChange
  bijective := bijective_restrictionEvaluation_of_basedIso E e f h
    C.isRepresentedBy_baseChange C.comp_eq_baseChange

@[simp] theorem baseChangeOfBasedIso_j (e : S_K ≅ S') (f : G_K ≅ H)
    (h : i_K ≫ f.hom = CommGroupScheme.groupHom e.hom ≫ j) :
    (C.baseChangeOfBasedIso E e f h).j = (GroupScheme.baseChange b).map C.j :=
  rfl

@[simp] theorem baseChangeOfBasedIso_s (e : S_K ≅ S') (f : G_K ≅ H)
    (h : i_K ≫ f.hom = CommGroupScheme.groupHom e.hom ≫ j) :
    (C.baseChangeOfBasedIso E e f h).s = (GroupScheme.baseChange b).map C.s :=
  rfl

end BaseChange

end CentralizerDatum

end Langlands.Geometry.Building
