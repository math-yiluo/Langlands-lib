import Langlands.AlgebraicGeometry.Modules.SerreVanishing.ChartOf

/-! # Section transport for restriction isomorphisms -/

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open Langlands.Scheme.Modules Langlands.SchemeModule.SectionClearing

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Modules

variable {S : Scheme.{u}} {M N : S.Modules} {U V : S.Opens}

/-- An isomorphism on an open subscheme, viewed on the slice of original opens. -/
def overRestrictionIso (f : M.restrict U.ι ≅ N.restrict U.ι) :
    M.over U ≅ N.over U :=
  (Scheme.Modules.overEquiv U).fullyFaithfulFunctor.preimageIso
    ((Scheme.Modules.overFunctorEquiv U).app M ≪≫ f ≪≫
      ((Scheme.Modules.overFunctorEquiv U).app N).symm)

@[simp]
lemma overRestrictionIso_refl :
    overRestrictionIso (Iso.refl (M.restrict U.ι)) = Iso.refl (M.over U) := by
  apply Iso.ext
  apply (Scheme.Modules.overEquiv U).functor.map_injective
  simp [overRestrictionIso]

@[simp]
lemma overRestrictionIso_symm (f : M.restrict U.ι ≅ N.restrict U.ι) :
    overRestrictionIso f.symm = (overRestrictionIso f).symm := by
  apply Iso.ext
  apply (Scheme.Modules.overEquiv U).functor.map_injective
  simp [overRestrictionIso]

lemma overRestrictionIso_trans {P : S.Modules}
    (f : M.restrict U.ι ≅ N.restrict U.ι)
    (g : N.restrict U.ι ≅ P.restrict U.ι) :
    overRestrictionIso (f ≪≫ g) = overRestrictionIso f ≪≫ overRestrictionIso g := by
  apply Iso.ext
  apply (Scheme.Modules.overEquiv U).functor.map_injective
  simp [overRestrictionIso]

lemma overRestrictionIso_hom_app
    (f : M.restrict U.ι ≅ N.restrict U.ι) (h : V ≤ U) (x : Γ(M, V)) :
    (overRestrictionIso f).hom.val.app (op (Over.mk (homOfLE h))) x =
      SerreVanishing.modE f V h x := by
  have hm := (Scheme.Modules.overEquiv U).fullyFaithfulFunctor.map_preimage
    (((Scheme.Modules.overFunctorEquiv U).app M ≪≫ f ≪≫
      ((Scheme.Modules.overFunctorEquiv U).app N).symm).hom)
  have ha := congrArg
    (fun g => g.app (U.ι ⁻¹ᵁ V)
      (ofImage M
        (M.presheaf.map (homOfLE (U.ι.image_preimage_le V)).op x))) hm
  change (overRestrictionIso f).hom.val.app
      (op (Over.mk (homOfLE (show U.ι ''ᵁ (U.ι ⁻¹ᵁ V) ≤ U from
        (U.ι.image_preimage_le V).trans h)))) (M.presheaf.map (homOfLE (U.ι.image_preimage_le V)).op x) =
    toImage N (f.hom.app (U.ι ⁻¹ᵁ V)
      (ofImage M
        (M.presheaf.map (homOfLE (U.ι.image_preimage_le V)).op x))) at ha
  unfold SerreVanishing.modE
  rw [← ha]
  have hn := PresheafOfModules.naturality_apply (overRestrictionIso f).hom.val
    (Over.homMk (homOfLE (U.ι.image_preimage_le V)) :
      Over.mk (homOfLE ((U.ι.image_preimage_le V).trans h)) ⟶
        Over.mk (homOfLE h)).op x
  change (overRestrictionIso f).hom.val.app
      (op (Over.mk (homOfLE ((U.ι.image_preimage_le V).trans h))))
        (M.presheaf.map (homOfLE (U.ι.image_preimage_le V)).op x) =
    N.presheaf.map (homOfLE (U.ι.image_preimage_le V)).op
      ((overRestrictionIso f).hom.val.app (op (Over.mk (homOfLE h))) x) at hn
  rw [hn, modules_map_map, modules_map_id]

end Langlands.AlgebraicGeometry.Modules
