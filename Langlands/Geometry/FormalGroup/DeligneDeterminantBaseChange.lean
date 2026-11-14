import Langlands.Geometry.FormalGroup.DelignePiStalkBaseChange
import Langlands.Geometry.FormalGroup.DeligneZeroLocusBaseChange

/-! # Transport of actual Deligne determinant lattices -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.DeligneFormalSpace

open CategoryTheory TopologicalSpace

variable {O : Type u} [CommRing O] (F : Type u) [Field F] [Algebra O F]

/-- The actual exterior-power map of an F-linear map between rational stalk modules. -/
def exteriorStalkMap (k : ℕ) {V W : ModuleCat.{u} F} (g : V ⟶ W) :
    ModuleCat.of F (⋀[F]^k V) ⟶ ModuleCat.of F (⋀[F]^k W) :=
  ModuleCat.ofHom (exteriorPower.map k g.hom)

/-- Taking the O-span of actual exterior products commutes with an F-linear map. -/
theorem exteriorStalkLattice_map (k : ℕ) {V W : ModuleCat.{u} F} (g : V ⟶ W)
    (L : Submodule O ((ModuleCat.restrictScalars (algebraMap O F)).obj V)) :
    (exteriorStalkLattice F k V L).map
        (((ModuleCat.restrictScalars (algebraMap O F)).map
          (exteriorStalkMap F k g)).hom) =
      exteriorStalkLattice F k W
        (L.map (((ModuleCat.restrictScalars (algebraMap O F)).map g).hom)) := by
  classical
  unfold exteriorStalkLattice
  rw [Submodule.map_span]
  congr 1
  ext z
  constructor
  · rintro ⟨_, ⟨v, rfl⟩, rfl⟩
    refine ⟨fun j => ⟨g (v j).val, ⟨(v j).val, (v j).property, rfl⟩⟩, ?_⟩
    change exteriorPower.ιMulti F k (fun j => g (v j).val) =
      exteriorPower.map k g.hom
        (exteriorPower.ιMulti F k (fun j => (v j).val))
    rw [exteriorPower.map_apply_ιMulti]
    rfl
  · rintro ⟨v, rfl⟩
    choose w hw heq using fun j => (v j).property
    refine ⟨exteriorPower.ιMulti F k w, ⟨fun j => ⟨w j, hw j⟩, rfl⟩, ?_⟩
    change exteriorPower.map k g.hom (exteriorPower.ιMulti F k w) =
      exteriorPower.ιMulti F k (fun j => (v j).val)
    rw [exteriorPower.map_apply_ιMulti]
    congr 1
    funext j
    exact heq j

/-- An F-linear map commutes with scalar multiplication of an O-lattice. -/
theorem scaleStalkLattice_map (a : F) {V W : ModuleCat.{u} F} (g : V ⟶ W)
    (L : Submodule O ((ModuleCat.restrictScalars (algebraMap O F)).obj V)) :
    (scaleStalkLattice F a V L).map
        (((ModuleCat.restrictScalars (algebraMap O F)).map g).hom) =
      scaleStalkLattice F a W
        (L.map (((ModuleCat.restrictScalars (algebraMap O F)).map g).hom)) := by
  unfold scaleStalkLattice
  rw [← Submodule.map_comp, ← Submodule.map_comp]
  congr 1
  apply LinearMap.ext
  intro v
  exact g.hom.map_smul a v

variable {X Y : TopCat.{u}} {d : ℕ} [NeZero d] {π : O}

namespace FramedLatticePiSheaf

variable (M : FramedLatticePiSheaf d π Y F)

/-- Every integer translate of the actual frame lattice is transported by inverse image. -/
theorem translatedFrameStalkLattice_pullback (f : X ⟶ Y)
    (hπ : algebraMap O F π ≠ 0) (n : ℤ) (x : X) :
    (M.translatedFrameStalkLattice F hπ n (f x)).map
        (((ModuleCat.restrictScalars (algebraMap O F)).map
          (rationalLatticeStalkPullbackIso F f M.lattice.sheaf x).hom).hom) =
      (M.inverseImage f).translatedFrameStalkLattice F hπ n x := by
  have h := congrArg
    (fun g => ((ModuleCat.restrictScalars (algebraMap O F)).map g).hom)
    (rationalPiStalkAut_zpow_pullback F f M.lattice.sheaf hπ n x)
  simp only [Functor.map_comp, ModuleCat.hom_comp] at h
  unfold translatedFrameStalkLattice
  rw [← Submodule.map_comp, h, Submodule.map_comp, M.frameStalkLattice_pullback F f x]
  rfl

/-- The literal pi^(-n) exterior determinant of every translated frame is transported. -/
theorem normalizedFrameDeterminant_pullback (f : X ⟶ Y)
    (hπ : algebraMap O F π ≠ 0) (n : ℤ) (x : X) :
    (M.normalizedFrameDeterminant F hπ n (f x)).map
        (((ModuleCat.restrictScalars (algebraMap O F)).map
          (exteriorStalkMap F d
            (rationalLatticeStalkPullbackIso F f M.lattice.sheaf x).hom)).hom) =
      (M.inverseImage f).normalizedFrameDeterminant F hπ n x := by
  unfold normalizedFrameDeterminant
  rw [scaleStalkLattice_map, exteriorStalkLattice_map,
    M.translatedFrameStalkLattice_pullback F f hπ n x]
  rfl

end FramedLatticePiSheaf

open _root_.AlgebraicGeometry

namespace SheafPreDatum

variable {F} {S S' : Scheme.{u}} {φ : O →+* Γ(S, ⊤)}
  (D : SheafPreDatum d π F φ)

/-- The exterior-power comparison between the actual total rational determinant stalks. -/
def determinantStalkPullbackMap (f : S' ⟶ S) (x : S') :
    ModuleCat.of F (⋀[F]^d
      (rationalLatticeStalk F (S : TopCat) d π D.eta.lattice.sheaf (f x))) ⟶
        ModuleCat.of F (⋀[F]^d
          (rationalLatticeStalk F (S' : TopCat) d π
            (D.pullback f).eta.lattice.sheaf x)) :=
  exteriorStalkMap F d
    (rationalLatticeStalkPullbackIso F f.base D.eta.lattice.sheaf x).hom

/-- The actual component determinant is transported by the exterior power of the stalk map. -/
theorem componentDeterminant_pullback (f : S' ⟶ S) (i : ZMod d) (x : S') :
    (D.componentDeterminant i (f x)).map
        (((ModuleCat.restrictScalars (algebraMap O F)).map
          (D.determinantStalkPullbackMap f x)).hom) =
      (D.pullback f).componentDeterminant i x := by
  unfold componentDeterminant determinantStalkPullbackMap
  rw [exteriorStalkLattice_map, D.eta.lattice.componentStalkLattice_pullback F f.base i x]
  rfl

/-- The all-integer actual determinant normalization is preserved by scheme base change. -/
theorem DeterminantNormalized.pullback (hπ : algebraMap O F π ≠ 0)
    (h : D.DeterminantNormalized hπ) (f : S' ⟶ S) :
    (D.pullback f).DeterminantNormalized hπ := by
  intro n x hx
  have hx' : f x ∈ D.tangent.graded.piZeroLocus (n : ZMod d) := by
    change x ∈ (D.tangent.pullback f).graded.piZeroLocus (n : ZMod d) at hx
    rw [D.tangent.piZeroLocus_pullback f (n : ZMod d)] at hx
    exact hx
  have heq := congrArg
    (fun L => L.map (((ModuleCat.restrictScalars (algebraMap O F)).map
      (D.determinantStalkPullbackMap f x)).hom))
    (h n (f x) hx')
  rw [D.componentDeterminant_pullback f (n : ZMod d) x] at heq
  dsimp only [determinantStalkPullbackMap] at heq
  rw [D.eta.normalizedFrameDeterminant_pullback F f.base hπ n x] at heq
  exact heq

end SheafPreDatum

end Langlands.DeligneFormalSpace
