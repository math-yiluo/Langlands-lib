import Langlands.Geometry.FormalGroup.RationalHeight
import Langlands.Geometry.FormalGroup.ScalarIsogenyPresentation

/-! # Transport of local rational heights by actual formal isomorphisms -/

noncomputable section

universe u v w

namespace Langlands.FormalGroup.ModuleLaw

open CategoryTheory Opposite TopologicalSpace TensorProduct AlgebraicGeometry

attribute [local instance] coefficientAlgebra coefficientScalarTower

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {F : Type v} [Field F] [Algebra O F]
variable {σ τ σ' τ' : Type} [Finite σ] [Finite τ] [Finite σ'] [Finite τ']
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ}
variable {M' : ModuleLaw O R σ'} {N' : ModuleLaw O R τ'}

namespace Hom

/-- Change both coordinates by the specified actual formal isomorphisms. -/
def isoTransport (a : Iso M M') (b : Iso N N') :
    Hom M N →ₗ[O] Hom M' N' where
  toFun f := b.hom.comp (f.comp a.inv)
  map_add' f g := by rw [add_comp, comp_add]
  map_smul' c f := by rw [smul_comp, comp_smul]; rfl

@[simp]
theorem isoTransport_apply (a : Iso M M') (b : Iso N N') (f : Hom M N) :
    isoTransport a b f = b.hom.comp (f.comp a.inv) := rfl

/-- Structural extension of an actual global formal map is coherent on tests. -/
theorem algebraMapLinear_map {A B : CommAlgCat.{w} R} (φ : A ⟶ B) (f : Hom M N) :
    algebraMapLinear φ (f.map (IsScalarTower.toAlgHom O R A)) =
      f.map (IsScalarTower.toAlgHom O R B) := by
  apply Hom.ext
  apply CommLaw.Hom.ext
  rw [algebraMapLinear_coordinates]
  change (f.toHom.toCoordinateMap.map (algebraMap R A)).map φ.hom.toRingHom =
    f.toHom.toCoordinateMap.map (algebraMap R B)
  rw [CoordinateMap.map_ringHom_comp]
  exact congrArg (fun g => f.toHom.toCoordinateMap.map g) (RingHom.ext φ.hom.commutes)

/-- Actual test restriction commutes with the chosen coordinate changes. -/
theorem algebraMapLinear_isoTransport {A B : CommAlgCat.{w} R} (φ : A ⟶ B)
    (a : Iso M M') (b : Iso N N')
    (f : Hom (M.overAlgebra A) (N.overAlgebra A)) :
    algebraMapLinear φ
        (isoTransport (a.map (IsScalarTower.toAlgHom O R A))
          (b.map (IsScalarTower.toAlgHom O R A)) f) =
      isoTransport (a.map (IsScalarTower.toAlgHom O R B))
        (b.map (IsScalarTower.toAlgHom O R B)) (algebraMapLinear φ f) := by
  simp only [isoTransport_apply, algebraMapLinear_hom_comp]
  change (algebraMapLinear φ (b.hom.map (IsScalarTower.toAlgHom O R A))).comp
    ((algebraMapLinear φ f).comp
      (algebraMapLinear φ (a.inv.map (IsScalarTower.toAlgHom O R A)))) =
    (b.hom.map (IsScalarTower.toAlgHom O R B)).comp
      ((algebraMapLinear φ f).comp (a.inv.map (IsScalarTower.toAlgHom O R B)))
  rw [algebraMapLinear_map, algebraMapLinear_map]

/-- The same represented kernel and fppf lifting condition survive the coordinate change. -/
theorem HasHeight.isoTransport {q n : ℕ} {f : Hom M N} (hf : f.HasHeight q n)
    (a : Iso M M') (b : Iso N N') : (Hom.isoTransport a b f).HasHeight q n := by
  apply hasHeight_of_isoSquare f (Hom.isoTransport a b f) a b
  · change (b.hom.comp (f.comp a.inv)).comp a.hom = _
    rw [comp_assoc, comp_assoc, a.inv_hom, comp_id]
  · exact hf

end Hom

namespace RationalHom

/-- Extend the actual integral coordinate change to the global tensor Hom. -/
def isoTransport (a : Iso M M') (b : Iso N N') :
    RationalHom F M N →ₗ[F] RationalHom F M' N' :=
  (Hom.isoTransport a b).baseChange F

@[simp]
theorem isoTransport_tmul (a : Iso M M') (b : Iso N N') (c : F) (f : Hom M N) :
    isoTransport a b (c ⊗ₜ[O] f) = c ⊗ₜ[O] Hom.isoTransport a b f :=
  LinearMap.baseChange_tmul _ _ _

@[simp]
theorem isoTransport_ofHom (a : Iso M M') (b : Iso N N') (f : Hom M N) :
    isoTransport a b (ofHom (F := F) f) = ofHom (Hom.isoTransport a b f) :=
  isoTransport_tmul a b 1 f

/-- The tensor coordinate change is composition with the actual rationalized isomorphisms. -/
theorem isoTransport_eq_comp (a : Iso M M') (b : Iso N N') (f : RationalHom F M N) :
    isoTransport a b f = comp (ofHom b.hom) (comp f (ofHom a.inv)) := by
  induction f using TensorProduct.inductionOn with
  | add f g hf hg => simp only [map_add, add_comp, comp_add, hf, hg]
  | tmul c f =>
    simp only [isoTransport_tmul, ofHom_apply, comp_tmul, mul_one, one_mul]
    rfl

/-- Tensor restriction on coefficient tests respects the actual coordinate changes. -/
theorem algebraMapLinear_isoTransport {A B : CommAlgCat.{v} R} (φ : A ⟶ B)
    (a : Iso M M') (b : Iso N N')
    (f : RationalHom F (M.overAlgebra A) (N.overAlgebra A)) :
    algebraMapLinear φ
        (isoTransport (a.map (IsScalarTower.toAlgHom O R A))
          (b.map (IsScalarTower.toAlgHom O R A)) f) =
      isoTransport (a.map (IsScalarTower.toAlgHom O R B))
        (b.map (IsScalarTower.toAlgHom O R B)) (algebraMapLinear φ f) := by
  induction f using TensorProduct.inductionOn with
  | add f g hf hg => simp only [map_add, hf, hg]
  | tmul c f =>
    simp only [isoTransport_tmul, algebraMapLinear_tmul, Hom.algebraMapLinear_isoTransport]

/-- Global tensor coefficient extension commutes with the actual coordinate changes. -/
theorem map_isoTransport {S : Type v} [CommRing S] [Algebra O S]
    (φ : R →ₐ[O] S) (a : Iso M M') (b : Iso N N') (f : RationalHom F M N) :
    map φ (isoTransport a b f) = isoTransport (a.map φ) (b.map φ) (map φ f) := by
  induction f using TensorProduct.inductionOn with
  | add f g hf hg => simp only [map_add, hf, hg]
  | tmul c f =>
    simp only [isoTransport_tmul, map_tmul, Hom.isoTransport_apply, Hom.map_comp]
    rfl

end RationalHom

/-- The specified formal coordinate changes give a natural map of actual rational Hom tests. -/
def rationalHomIsoTransport (a : Iso M M') (b : Iso N N') :
    rationalHomFunctor F M N ⟶ rationalHomFunctor F M' N' where
  app A := ModuleCat.ofHom
    (RationalHom.isoTransport (a.map (IsScalarTower.toAlgHom O R A))
      (b.map (IsScalarTower.toAlgHom O R A)))
  naturality {A B} φ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    exact (RationalHom.algebraMapLinear_isoTransport φ a b f).symm

namespace RationalSection

/-- Transport actual rational Hom sections using functorial sheafification. -/
def isoTransport (a : Iso M M') (b : Iso N N') (U : Opens (PrimeSpectrum R)) :
    RationalSection F M N U →ₗ[F] RationalSection F M' N' U :=
  ((sheafifyMap (Opens.grothendieckTopology (PrimeSpectrum.Top R))
    (Functor.whiskerLeft (coefficientStructurePresheaf R)
      (rationalHomIsoTransport (F := F) a b))).app (op U)).hom

/-- The sheafified coordinate change is the specified tensor change on presheaf sections. -/
theorem isoTransport_ofRational (a : Iso M M') (b : Iso N N')
    (U : Opens (PrimeSpectrum R)) (f : (rationalHomPresheaf F M N).obj (op U)) :
    isoTransport a b U (ofRational U f) =
      ofRational U
        (RationalHom.isoTransport
          (a.map (IsScalarTower.toAlgHom O R ((coefficientStructurePresheaf R).obj (op U))))
          (b.map (IsScalarTower.toAlgHom O R ((coefficientStructurePresheaf R).obj (op U)))) f) := by
  exact (congrArg (fun k => (k.app (op U)).hom f)
    (toSheafify_naturality (Opens.grothendieckTopology (PrimeSpectrum.Top R))
      (Functor.whiskerLeft (coefficientStructurePresheaf R)
        (rationalHomIsoTransport (F := F) a b)))).symm

/-- Integral sections transport by the actual integral formal maps. -/
theorem isoTransport_ofIntegral (a : Iso M M') (b : Iso N N')
    (U : Opens (PrimeSpectrum R)) (f : OpenIntegralHom M N U) :
    isoTransport a b U (ofIntegral U f : RationalSection F M N U) =
      ofIntegral U
        (Hom.isoTransport
          (a.map (IsScalarTower.toAlgHom O R ((coefficientStructurePresheaf R).obj (op U))))
          (b.map (IsScalarTower.toAlgHom O R ((coefficientStructurePresheaf R).obj (op U)))) f) := by
  exact (isoTransport_ofRational a b U (RationalHom.ofHom (F := F) f)).trans
    (congrArg (ofRational (F := F) U) (RationalHom.isoTransport_ofHom _ _ f))

/-- The specified sheafified coordinate change commutes with restriction to every open. -/
theorem restrict_isoTransport (a : Iso M M') (b : Iso N N')
    {U V : Opens (PrimeSpectrum R)} (i : V ⟶ U) (z : RationalSection F M N U) :
    restrict i (isoTransport a b U z) = isoTransport a b V (restrict i z) := by
  exact (congrArg (fun k => k.hom z)
    ((sheafifyMap (Opens.grothendieckTopology (PrimeSpectrum.Top R))
      (Functor.whiskerLeft (coefficientStructurePresheaf R)
        (rationalHomIsoTransport (F := F) a b))).naturality i.op)).symm

/-- The global tensor and section coordinate changes define the same actual section. -/
theorem isoTransport_ofGlobal (a : Iso M M') (b : Iso N N') (z : RationalHom F M N) :
    isoTransport a b ⊤ (ofGlobal z) = ofGlobal (RationalHom.isoTransport a b z) := by
  exact (isoTransport_ofRational a b ⊤
    (RationalHom.map
      (IsScalarTower.toAlgHom O R ((coefficientStructurePresheaf R).obj (op ⊤))) z)).trans
    (congrArg (ofRational (F := F) ⊤) (RationalHom.map_isoTransport _ a b z).symm)

namespace HeightPresentation

variable {π : O} {q : ℕ} {U : Opens (PrimeSpectrum R)}
variable {z : RationalSection F M N U}

/-- Retain both rank exponents and the scalar denominator under actual formal isomorphisms. -/
def isoTransport (P : HeightPresentation π q z) (a : Iso M M') (b : Iso N N') :
    HeightPresentation π q (RationalSection.isoTransport a b U z) where
  exponent := P.exponent
  representative := Hom.isoTransport
    (a.map (IsScalarTower.toAlgHom O R ((coefficientStructurePresheaf R).obj (op U))))
    (b.map (IsScalarTower.toAlgHom O R ((coefficientStructurePresheaf R).obj (op U))))
      P.representative
  numeratorHeight := P.numeratorHeight
  denominatorHeight := P.denominatorHeight
  numerator := P.numerator.isoTransport _ _
  denominator := by
    let aU := a.map
      (IsScalarTower.toAlgHom O R ((coefficientStructurePresheaf R).obj (op U)))
    exact Hom.hasHeight_of_isoSquare _ _ aU aU
      (aU.hom.comp_scalarHom _).symm P.denominator
  represents := by
    have h := congrArg (RationalSection.isoTransport a b U) P.represents
    simpa only [map_smul, isoTransport_ofIntegral] using h

@[simp]
theorem index_isoTransport (P : HeightPresentation π q z) (a : Iso M M') (b : Iso N N') :
    (P.isoTransport a b).index = P.index := rfl

end HeightPresentation

namespace HasHeightFunction

variable {π : O} {q : ℕ} {U : Opens (PrimeSpectrum R)}
variable {z : RationalSection F M N U} {h : U → ℤ}

/-- The same local signed kernel-rank function survives the specified formal coordinate change. -/
theorem isoTransport (hz : HasHeightFunction π q z h) (a : Iso M M') (b : Iso N N') :
    HasHeightFunction π q (RationalSection.isoTransport a b U z) h := by
  intro x
  obtain ⟨V, hx, i, P, hP⟩ := hz x
  have he := (restrict_isoTransport a b i z).symm
  refine ⟨V, hx, i, he ▸ P.isoTransport a b, ?_⟩
  intro y
  rw [HeightPresentation.index_cast, HeightPresentation.index_isoTransport]
  exact hP y

/-- In particular, changing the coordinates of an actual global tensor preserves its local height. -/
theorem ofGlobal_isoTransport {z : RationalHom F M N} {h : (⊤ : Opens (PrimeSpectrum R)) → ℤ}
    (hz : HasHeightFunction π q (ofGlobal z) h) (a : Iso M M') (b : Iso N N') :
    HasHeightFunction π q (ofGlobal (RationalHom.isoTransport a b z)) h := by
  rw [← isoTransport_ofGlobal]
  exact hz.isoTransport a b

end HasHeightFunction
end RationalSection

end Langlands.FormalGroup.ModuleLaw
