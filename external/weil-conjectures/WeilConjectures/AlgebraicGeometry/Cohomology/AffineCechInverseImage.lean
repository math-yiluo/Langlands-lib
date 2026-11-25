/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Cohomology.FlatCohomologyCechBaseChange
import WeilConjectures.AlgebraicGeometry.Cohomology.CechComparisonAffine
import WeilConjectures.AlgebraicGeometry.Cohomology.CechComparisonInverseImage

/-! # Inverse image on affine Čech cocycles

Source: Stacks Project, Tags 01FD, 01ET and 01XD.
(blueprint: lem-pc-affine-cech-inverse-image)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency.types false in
/-- Leray comparisons respect any inverse-image coefficient map on matching cocycles.
This is a statement about sections and inverse image only, without tensor products.

Source: Stacks Project, Tag 01FD (functoriality of the Čech comparison),
Tags 01ET and 01XD (affine acyclicity).
(blueprint: lem-pc-affine-cech-inverse-image)

Proof: Choose injective resolutions of the underlying abelian sheaves. The
coefficient map M -> g_*N lifts into a resolution of the pushed-forward target
resolution, giving a comparison of augmented Čech double complexes. Restriction
commutes with the resolution maps. The coordinate matching hypothesis identifies
the original cocycle in the source augmentation with the target cocycle in this
comparison. Injective Čech acyclicity identifies the total cohomology with sheaf
cohomology. Affine-intersection acyclicity makes both coefficient Čech edge maps
isomorphisms. Multiplication by a global function commutes with every augmentation
and comparison, making the edge maps linear over the global-function rings and
hence over the displayed bases. The comparison on sheaf cohomology is obtained by
applying exact inverse image to Ext, precomposing with the constant integer sheaf
isomorphism, and postcomposing with the adjoint coefficient map; thus it is the
right side of the formula. The augmentation diagram then gives the claimed
identity. The same argument applies in degree zero, when it is the section map;
empty covers force empty schemes and zero cohomology. No finiteness of the cover,
flatness, affine property of g, or chain-map invertibility is needed. -/
theorem exists_affineCech_inverseImage
    {R S : Type u} [CommRing R] [CommRing S] {X Y : Scheme.{u}} {ι : Type u}
    (g : Y ⟶ X) (f : X ⟶ Spec (.of R)) (f' : Y ⟶ Spec (.of S))
    (U : ι → X.Opens) (V : ι → Y.Opens)
    (hU : ∀ (k : ℕ) (y : Fin (k + 1) → ι), IsAffineOpen (⨅ l, U (y l)))
    (hV : ∀ (k : ℕ) (y : Fin (k + 1) → ι), IsAffineOpen (⨅ l, V (y l)))
    (hcover : iSup U = ⊤) (hcover' : iSup V = ⊤)
    (M : X.Modules) (N : Y.Modules) [M.IsQuasicoherent] [N.IsQuasicoherent]
    (φ : M ⟶ (pushforward g).obj N) (q : ℕ)
    (hinter : ∀ (k : ℕ) (y : Fin (k + 1) → ι),
      (⨅ l, V (y l)) ≤ g ⁻¹ᵁ (⨅ l, U (y l))) :
    ∃ e : (cechOver f U M).homology q ≅ ModuleCat.of R (HOver f M q),
    ∃ e' : (cechOver f' V N).homology q ≅ ModuleCat.of S (HOver f' N q),
    ∀ (z : (cechOver f U M).cycles q) (z' : (cechOver f' V N).cycles q),
      (∀ y : Fin (q + 1) → ι,
        cechCoordinate f' V N q y ((cechOver f' V N).iCycles q z') =
          N.presheaf.map (homOfLE (hinter q y)).op
            (φ.val.app (op (⨅ l, U (y l)))
              (cechCoordinate f U M q y ((cechOver f U M).iCycles q z)))) →
      e'.hom ((cechOver f' V N).homologyπ q z') =
        Sheaf.H.map (coeff g φ) q
          (Sheaf.H.mapFunctor (invImage g) (constIso g).symm
            ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) q
              (e.hom ((cechOver f U M).homologyπ q z))) := by
  let := cohomologyHasSheafify X
  let := cohomologyHasSheafify Y
  let := cohomologyHasExt X
  let := cohomologyHasExt Y
  obtain ⟨c, c', hc⟩ := exists_cechComparison_inverseImage g f f' U V
    hcover hcover' M N φ hinter
  obtain ⟨hbij, hsmul⟩ := cechComparison_affine_bijective_linear f U hU hcover c M q
  obtain ⟨hbij', hsmul'⟩ := cechComparison_affine_bijective_linear f' V hV hcover' c' N q
  let l : (cechOver f U M).homology q →ₗ[R] HOver f M q :=
    { c.overMap f M q with map_smul' := hsmul }
  let l' : (cechOver f' V N).homology q →ₗ[S] HOver f' N q :=
    { c'.overMap f' N q with map_smul' := hsmul' }
  refine ⟨(LinearEquiv.ofBijective l hbij).toModuleIso,
    (LinearEquiv.ofBijective l' hbij').toModuleIso, ?_⟩
  exact hc q

end AlgebraicGeometry.Scheme.Modules
