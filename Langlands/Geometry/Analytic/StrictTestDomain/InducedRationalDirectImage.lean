import Langlands.Geometry.Analytic.StrictTestDomain.InducedRationalSpectrum
import Langlands.Sheaf.Equivariant.DirectImage

/-! # Full sheaf variation along actual induced rational transport maps -/

noncomputable section

universe u v a b r w t

namespace Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction

open CategoryTheory TopologicalSpace Opposite
open Langlands.Sheaf.Equivariant

attribute [local instance] NormContinuousAffinoidAction.topCatSelfForget

section General

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedStrictAffinoidAlgebra K}
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ρ : RationalSpectralAction G P}

namespace OpenSubgroupTransport.SheafVariation

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- Equal actual continuous maps give the same full direct-image functor. -/
private theorem directImage_congr
    {S T : Type t} [TopologicalSpace S] [TopologicalSpace T]
    [MulAction G S] [MulAction G T]
    {p q : C(S, T)} (hp : ∀ (g : G) (x : S), p (g • x) = g • p x)
    (hq : ∀ (g : G) (x : S), q (g • x) = g • q x)
    (A : Type a) [Category.{b} A] (h : p = q) :
    DirectImage.sheaf p hp A = DirectImage.sheaf q hq A := by
  subst q
  rfl

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- The coefficient map respects equality of the original continuous maps. -/
private theorem coefficientMap_congr
    {S T : Type t} [TopologicalSpace S] [TopologicalSpace T]
    [MulAction G S] [MulAction G T]
    [ContinuousConstSMul G S] [ContinuousConstSMul G T]
    {p q : C(S, T)} (hp : ∀ (g : G) (x : S), p (g • x) = g • p x)
    (hq : ∀ (g : G) (x : S), q (g • x) = g • q x)
    {R : Type r} [CommRing R] {M : Type w} [AddCommGroup M] [Module R M]
    (h : p = q) (τ : Representation R G M) :
    DirectImage.coefficientMap p hp τ ≫
        (eqToIso (directImage_congr hp hq (ModuleCat.{max t w} R) h)).hom.app
          (LocallyConstantSheaf.sheaf (X := S) τ) =
      DirectImage.coefficientMap q hq τ := by
  subst q
  simp

variable {X Y Z : ρ.OpenSubgroupTransport}

/-- The actual continuous identity transport map is the identity on the quotient. -/
theorem inducedMap_id_eq (X : ρ.OpenSubgroupTransport) :
    (𝟙 X : X ⟶ X).inducedMap = ContinuousMap.id X.InducedSpectrum :=
  ContinuousMap.ext (Hom.inducedMap_id X)

/-- Actual continuous transport maps compose in their original order. -/
theorem inducedMap_comp_eq (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).inducedMap = g.inducedMap.comp f.inducedMap :=
  ContinuousMap.ext (Hom.inducedMap_comp f g)

/-- Inverse opens under the actual map `[a,x] ↦ [a label⁻¹, localMap x]`. -/
def preimage (f : X ⟶ Y) :
    ActionOpens G Y.InducedSpectrum ⥤ ActionOpens G X.InducedSpectrum :=
  DirectImage.preimage f.inducedMap f.inducedMap_smul

@[simp]
theorem mem_preimage (f : X ⟶ Y) (U : ActionOpens G Y.InducedSpectrum)
    (z : X.InducedSpectrum) :
    z ∈ ((preimage f).obj U).openSet ↔ f.inducedMap z ∈ U.openSet := Iff.rfl

/-- The inverse open formula retains the original rational transport label correction. -/
@[simp]
theorem inducedMk_mem_preimage (f : X ⟶ Y) (U : ActionOpens G Y.InducedSpectrum)
    (a : G) (x : X.LocalSpectrum) :
    X.inducedMk a x ∈ ((preimage f).obj U).openSet ↔
      Y.inducedMk (a * f.label⁻¹) (f.localSpectrumMap x) ∈ U.openSet := by
  change f.inducedMap (X.inducedMk a x) ∈ U.openSet ↔ _
  rw [Hom.inducedMap_mk]

@[simp]
theorem preimage_map_label (f : X ⟶ Y)
    {U V : ActionOpens G Y.InducedSpectrum} (k : U ⟶ V) :
    ((preimage f).map k).label = k.label := rfl

variable (A : Type a) [Category.{b} A]

/-- Full ordinary-open equivariant sheaf direct image along actual rational transport. -/
def directImage (f : X ⟶ Y) :
    TopologicalSheaf G X.InducedSpectrum A ⥤ TopologicalSheaf G Y.InducedSpectrum A :=
  DirectImage.sheaf f.inducedMap f.inducedMap_smul A

@[simp]
theorem directImage_obj_obj (f : X ⟶ Y) (F : TopologicalSheaf G X.InducedSpectrum A)
    (U : ActionOpens G Y.InducedSpectrum) :
    ((directImage A f).obj F).obj.obj (op U) =
      F.obj.obj (op ((preimage f).obj U)) := rfl

@[simp]
theorem directImage_obj_map (f : X ⟶ Y) (F : TopologicalSheaf G X.InducedSpectrum A)
    {U V : ActionOpens G Y.InducedSpectrum} (k : U ⟶ V) :
    ((directImage A f).obj F).obj.map k.op =
      F.obj.map ((preimage f).map k).op := rfl

@[simp]
theorem directImage_map_app (f : X ⟶ Y)
    {F F' : TopologicalSheaf G X.InducedSpectrum A} (k : F ⟶ F')
    (U : ActionOpens G Y.InducedSpectrum) :
    ((directImage A f).map k).hom.app (op U) =
      k.hom.app (op ((preimage f).obj U)) := rfl

/-- Forgetting rational-spectrum equivariance gives the original ordinary direct image. -/
def toSheafIso (f : X ⟶ Y) :
    directImage A f ⋙ toSheaf G Y.InducedSpectrum A ≅
      toSheaf G X.InducedSpectrum A ⋙
        TopCat.Sheaf.pushforward A (TopCat.ofHom f.inducedMap) := Iso.refl _

/-- Identity rational transport retains every original sheaf and morphism. -/
def directImageIdIso (X : ρ.OpenSubgroupTransport) :
    directImage A (𝟙 X) ≅ 𝟭 (TopologicalSheaf G X.InducedSpectrum A) :=
  eqToIso (directImage_congr (Hom.inducedMap_smul (𝟙 X))
    (fun (_ : G) (_ : X.InducedSpectrum) => rfl) A (inducedMap_id_eq X))

/-- Rational transport composition retains the full composite direct image. -/
def directImageCompIso (f : X ⟶ Y) (g : Y ⟶ Z) :
    directImage A (f ≫ g) ≅ directImage A f ⋙ directImage A g :=
  eqToIso (directImage_congr (Hom.inducedMap_smul (f ≫ g))
    (fun k x => by
      change g.inducedMap (f.inducedMap (k • x)) = k • g.inducedMap (f.inducedMap x)
      rw [f.inducedMap_smul, g.inducedMap_smul]) A (inducedMap_comp_eq f g))

section Coefficients

variable {R : Type r} [CommRing R] {M : Type w} [AddCommGroup M] [Module R M]

/-- Every full coefficient section is precomposed with the actual rational map. -/
def coefficientMap (f : X ⟶ Y) (τ : Representation R G M) :
    LocallyConstantSheaf.sheaf (X := Y.InducedSpectrum) τ ⟶
      (directImage (ModuleCat.{max (max u v) w} R) f).obj
        (LocallyConstantSheaf.sheaf (X := X.InducedSpectrum) τ) :=
  DirectImage.coefficientMap f.inducedMap f.inducedMap_smul τ

@[simp]
theorem coefficientMap_apply (f : X ⟶ Y) (τ : Representation R G M)
    (U : ActionOpens G Y.InducedSpectrum) (s : LocallyConstant U.openSet M)
    (z : ((preimage f).obj U).openSet) :
    LocallyConstant.toFun (((coefficientMap f τ).hom.app (op U)).hom s) z =
      s (DirectImage.pointMap f.inducedMap f.inducedMap_smul U z) := rfl

/-- On quotient representatives, precomposition includes the original inverse label. -/
theorem coefficientMap_mk_apply (f : X ⟶ Y) (τ : Representation R G M)
    (U : ActionOpens G Y.InducedSpectrum) (s : LocallyConstant U.openSet M)
    (a : G) (x : X.LocalSpectrum)
    (h : X.inducedMk a x ∈ ((preimage f).obj U).openSet) :
    LocallyConstant.toFun (((coefficientMap f τ).hom.app (op U)).hom s)
        ⟨X.inducedMk a x, h⟩ =
      s ⟨Y.inducedMk (a * f.label⁻¹) (f.localSpectrumMap x),
        (inducedMk_mem_preimage f U a x).mp h⟩ := by
  change s ⟨f.inducedMap (X.inducedMk a x), h⟩ = _
  congr 1
  apply Subtype.ext
  exact Hom.inducedMap_mk f a x

/-- Full locally constant coefficient sheaves, at each actual rational object. -/
def coefficientFunctor (X : ρ.OpenSubgroupTransport) (R : Type r) [CommRing R] :
    Rep.{w} R G ⥤
      TopologicalSheaf G X.InducedSpectrum (ModuleCat.{max (max u v) w} R) :=
  LocallyConstantSheaf.functor R G X.InducedSpectrum

@[simp]
theorem coefficientFunctor_map_app {M N : Rep.{w} R G} (c : M ⟶ N)
    (U : ActionOpens G X.InducedSpectrum) (s : LocallyConstant U.openSet M)
    (z : U.openSet) :
    LocallyConstant.toFun
      (((coefficientFunctor X R).map c).hom.app (op U) s) z = c.hom (s z) := rfl

/-- Rational-object variation is natural in every original coefficient intertwiner. -/
def coefficientNatTrans (f : X ⟶ Y) :
    coefficientFunctor Y R ⟶
      coefficientFunctor X R ⋙ directImage (ModuleCat.{max (max u v) w} R) f :=
  DirectImage.coefficientNatTrans f.inducedMap f.inducedMap_smul

/-- Identity transport gives the identity after the actual direct-image comparison. -/
@[simp]
theorem coefficientMap_id (X : ρ.OpenSubgroupTransport) (τ : Representation R G M) :
    coefficientMap (𝟙 X) τ ≫
      (directImageIdIso (ModuleCat.{max (max u v) w} R) X).hom.app
        (LocallyConstantSheaf.sheaf (X := X.InducedSpectrum) τ) =
      𝟙 (LocallyConstantSheaf.sheaf (X := X.InducedSpectrum) τ) := by
  exact
    (coefficientMap_congr (Hom.inducedMap_smul (𝟙 X))
      (fun (_ : G) (_ : X.InducedSpectrum) => rfl) (inducedMap_id_eq X) τ).trans
        (DirectImage.coefficientMap_id τ)

/-- Composition uses the original rational maps and full direct-image comparison. -/
theorem coefficientMap_comp (f : X ⟶ Y) (g : Y ⟶ Z) (τ : Representation R G M) :
    coefficientMap (f ≫ g) τ ≫
        (directImageCompIso (ModuleCat.{max (max u v) w} R) f g).hom.app
          (LocallyConstantSheaf.sheaf (X := X.InducedSpectrum) τ) =
      coefficientMap g τ ≫
        (directImage (ModuleCat.{max (max u v) w} R) g).map (coefficientMap f τ) := by
  exact
    (coefficientMap_congr (Hom.inducedMap_smul (f ≫ g))
      (fun k x => by
        change g.inducedMap (f.inducedMap (k • x)) = k • g.inducedMap (f.inducedMap x)
        rw [f.inducedMap_smul, g.inducedMap_smul]) (inducedMap_comp_eq f g) τ).trans
          (DirectImage.coefficientMap_comp f.inducedMap f.inducedMap_smul
            g.inducedMap g.inducedMap_smul τ)

end Coefficients

end OpenSubgroupTransport.SheafVariation

end General

section Ambient

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedStrictAffinoidAlgebra K}
  {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ρ : RationalSpectralAction G P}

namespace OpenSubgroupTransport.SheafVariation

variable {X Y : ρ.OpenSubgroupTransport} (A : Type a) [Category.{b} A]

/-- Direct image along the actual structural map to the ambient Banach spectrum. -/
def ambientDirectImage (X : ρ.OpenSubgroupTransport) :
    TopologicalSheaf G X.InducedSpectrum A ⥤
      TopologicalSheaf G (AmbientSpectrum ρ) A :=
  DirectImage.sheaf X.ambientMap X.ambientMap_smul A

/-- Every rational transport direct image lies over the same ambient spectrum. -/
def ambientDirectImageIso (f : X ⟶ Y) :
    directImage A f ⋙ ambientDirectImage A Y ≅ ambientDirectImage A X :=
  eqToIso (directImage_congr (p := Y.ambientMap.comp f.inducedMap)
    (fun k x => by
      change Y.ambientMap (f.inducedMap (k • x)) = k • Y.ambientMap (f.inducedMap x)
      rw [f.inducedMap_smul, Y.ambientMap_smul])
    X.ambientMap_smul A (ContinuousMap.ext (Hom.ambientMap_inducedMap f)))

section Coefficients

variable {R : Type r} [CommRing R] {M : Type w} [AddCommGroup M] [Module R M]

/-- Ambient coefficient sections pull back along the actual structural map. -/
def ambientCoefficientMap (X : ρ.OpenSubgroupTransport) (τ : Representation R G M) :
    LocallyConstantSheaf.sheaf (X := AmbientSpectrum ρ) τ ⟶
      (ambientDirectImage (ModuleCat.{max u w} R) X).obj
        (LocallyConstantSheaf.sheaf (X := X.InducedSpectrum) τ) :=
  DirectImage.coefficientMap X.ambientMap X.ambientMap_smul τ

/-- Full coefficient naturality also holds for the actual ambient map. -/
def ambientCoefficientNatTrans (X : ρ.OpenSubgroupTransport) :
    LocallyConstantSheaf.functor R G (AmbientSpectrum ρ) ⟶
      coefficientFunctor X R ⋙ ambientDirectImage (ModuleCat.{max u w} R) X :=
  DirectImage.coefficientNatTrans X.ambientMap X.ambientMap_smul

set_option maxHeartbeats 800000 in
/-- Rational coefficient variation agrees with the common ambient structural map. -/
theorem ambientCoefficientMap_transport (f : X ⟶ Y) (τ : Representation R G M) :
    (ambientCoefficientMap Y τ ≫
        (ambientDirectImage (ModuleCat.{max u w} R) Y).map (coefficientMap f τ)) ≫
          (ambientDirectImageIso (ModuleCat.{max u w} R) f).hom.app
            (LocallyConstantSheaf.sheaf (X := X.InducedSpectrum) τ) =
      ambientCoefficientMap X τ := by
  exact (congrArg (fun k => k ≫
      (ambientDirectImageIso (ModuleCat.{max u w} R) f).hom.app
        (LocallyConstantSheaf.sheaf (X := X.InducedSpectrum) τ))
      (DirectImage.coefficientMap_comp f.inducedMap f.inducedMap_smul
        Y.ambientMap Y.ambientMap_smul τ).symm).trans
    (coefficientMap_congr (p := Y.ambientMap.comp f.inducedMap)
      (fun k x => by
        change Y.ambientMap (f.inducedMap (k • x)) = k • Y.ambientMap (f.inducedMap x)
        rw [f.inducedMap_smul, Y.ambientMap_smul])
      X.ambientMap_smul (ContinuousMap.ext (Hom.ambientMap_inducedMap f)) τ)

end Coefficients

end OpenSubgroupTransport.SheafVariation

end Ambient

end Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction
