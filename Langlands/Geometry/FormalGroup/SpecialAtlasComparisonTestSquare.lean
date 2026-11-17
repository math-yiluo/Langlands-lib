import Langlands.Geometry.FormalGroup.SpecialAtlasComparisonTestComposition
import Langlands.Geometry.FormalGroup.AtlasOrderBaseChangeAlongSquare

/-! # Actual refined test comparisons around commuting coefficient squares -/

noncomputable section

universe u v w s

namespace Langlands.FormalGroup.ModuleLaw.OrderAction.Iso

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {D : Type w} [Ring D] [Algebra O D]
variable {σ τ υ ω ρ χ : Type} [Finite σ] [Finite τ] [Finite υ] [Finite ω] [Finite ρ] [Finite χ]
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ}
variable {P : ModuleLaw O R υ} {Q : ModuleLaw O R ω}
variable {U : ModuleLaw O R ρ} {V : ModuleLaw O R χ}
variable {E : OrderAction D M} {E' : OrderAction D N}
variable {E'' : OrderAction D P} {E''' : OrderAction D Q}
variable {E₄ : OrderAction D U} {E₅ : OrderAction D V}

/-- Paste specified squares of actual integral formal isomorphisms. -/
theorem square_paste {f : Iso E E'} {r : Iso E' E''} {l : Iso E E'''} {d : Iso E''' E''}
    {r' : Iso E'' E₄} {l' : Iso E''' E₅} {d' : Iso E₅ E₄}
    (h : f.trans r = l.trans d) (h' : d.trans r' = l'.trans d') :
    f.trans (r.trans r') = (l.trans l').trans d' := by
  apply ext_hom
  have h₁ := congrArg Iso.hom h
  have h₂ := congrArg Iso.hom h'
  change (r'.hom.comp r.hom).comp f.hom = d'.hom.comp (l'.hom.comp l.hom)
  calc
    (r'.hom.comp r.hom).comp f.hom = r'.hom.comp (r.hom.comp f.hom) := Hom.comp_assoc _ _ _
    _ = r'.hom.comp (d.hom.comp l.hom) := congrArg (fun z => r'.hom.comp z) h₁
    _ = (r'.hom.comp d.hom).comp l.hom := (Hom.comp_assoc _ _ _).symm
    _ = (d'.hom.comp l'.hom).comp l.hom := congrArg (fun z => z.comp l.hom) h₂
    _ = d'.hom.comp (l'.hom.comp l.hom) := Hom.comp_assoc _ _ _

/-- Reverse the two vertical actual integral maps in a proved square. -/
theorem square_reverse {f : Iso E E'} {r : Iso E' E''} {l : Iso E E'''} {d : Iso E''' E''}
    (h : f.trans r = l.trans d) : d.trans r.symm = l.symm.trans f := by
  apply ext_hom
  have ht := congrArg Iso.hom h
  change r.hom.comp f.hom = d.hom.comp l.hom at ht
  change r.inv.comp d.hom = f.hom.comp l.inv
  calc
    r.inv.comp d.hom = r.inv.comp (d.hom.comp (l.hom.comp l.inv)) := by
      rw [l.hom_inv, Hom.comp_id]
    _ = (r.inv.comp (d.hom.comp l.hom)).comp l.inv := by
      simp only [Hom.comp_assoc]
    _ = (r.inv.comp (r.hom.comp f.hom)).comp l.inv := by rw [← ht]
    _ = f.hom.comp l.inv := by rw [← Hom.comp_assoc r.inv, r.inv_hom, Hom.id_comp]

end Langlands.FormalGroup.ModuleLaw.OrderAction.Iso

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction.Iso

open CategoryTheory

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {D : Type w} [Ring D] [Algebra O D]
variable {σ τ υ : Type} [Finite σ] [Finite τ] [Finite υ]
variable {X : BasicAtlas O R σ} {Y : BasicAtlas O R τ} {Z : BasicAtlas O R υ}
variable {E : OrderAction D X} {E' : OrderAction D Y} {E'' : OrderAction D Z}
variable {h : X.opens = Y.opens} {k : Y.opens = Z.opens}

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- Restrict composition of actual integral atlas isomorphisms to the specified test chart. -/
theorem onChart_trans (f : Iso E E' h) (g : Iso E' E'' k)
    (C : CommAlgCat.{v} R) (b : Z.opens) (hb : IsUnit (algebraMap R C b.val)) :
    (f.trans g).onChart C b hb =
      (f.onChart C (sourceChart (X := Y) (Y := Z) k b) hb).trans (g.onChart C b hb) := by
  apply ModuleLaw.OrderAction.Iso.ext_hom
  rfl

/-- Restrict the actual inverse atlas map to the corresponding test chart. -/
theorem onChart_symm (f : Iso E E' h)
    (C : CommAlgCat.{v} R) (b : X.opens) (hb : IsUnit (algebraMap R C b.val)) :
    f.symm.onChart C b hb =
      (f.onChart C (sourceChart (X := Y) (Y := X) h.symm b) hb).symm := by
  apply ModuleLaw.OrderAction.Iso.ext_hom
  rfl

end Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction.Iso

namespace Langlands.FormalGroup.LocalDivision.SpecialAtlas

open CategoryTheory ValuativeRel CentralDivision ModuleLaw

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] {ι : L →ₐ[K] D}
variable {R S S' T : Type v} [CommRing R] [CommRing S] [CommRing S'] [CommRing T]
variable [Algebra 𝒪[K] R] [Algebra 𝒪[K] S] [Algebra 𝒪[K] S'] [Algebra 𝒪[K] T]
variable {X Y : SpecialAtlas K D ι R}

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- Equal coefficient maps give the same actual test comparison through the forced identity maps. -/
theorem testIso_baseAlongEq (c : Comparison X Y) {f g : R →ₐ[𝒪[K]] T} (e : f = g)
    (A : CommAlgCat.{v} T) (b : (baseChangeAlongComparison c f).right.opens)
    (hb : IsUnit (algebraMap T A b.val)) (b' : (baseChangeAlongComparison c g).right.opens)
    (hb' : IsUnit (algebraMap T A b'.val))
    (x : (X.baseChangeAlong g).atlas.opens) (y : (Y.baseChangeAlong g).atlas.opens)
    (hx : IsUnit (algebraMap T A x.val)) (hy : IsUnit (algebraMap T A y.val)) :
    ((baseChangeAlongComparison c f).testIso A b hb
      (BasicAtlas.sourceChart (X.atlas.baseAlongEqOpens_eq e) x)
      (BasicAtlas.sourceChart (Y.atlas.baseAlongEqOpens_eq e) y) hx hy).trans
        ((Y.order.baseAlongEqIso e).onChart A y hy) =
      ((X.order.baseAlongEqIso e).onChart A x hx).trans
        ((baseChangeAlongComparison c g).testIso A b' hb' x y hx hy) := by
  cases e
  apply ModuleLaw.OrderAction.Iso.ext_hom
  apply Subtype.ext
  apply ModuleLaw.Hom.ext
  apply CommLaw.Hom.ext
  change CoordinateMap.id.comp
      ((baseChangeAlongComparison c f).testIso A b hb x y hx hy).hom.val.toHom.toCoordinateMap =
    ((baseChangeAlongComparison c f).testIso A b' hb' x y hx hy).hom.val.toHom.toCoordinateMap.comp
      CoordinateMap.id
  simp only [CoordinateMap.id_comp, CoordinateMap.comp_id]
  exact congrArg (fun z => z.hom.val.toHom.toCoordinateMap)
    ((baseChangeAlongComparison c f).testIso_independent A b b' hb hb' x y hx hy)

set_option backward.isDefEq.respectTransparency false in
/-- Actual refined test comparisons commute with the canonical maps around a supplied coefficient square. -/
theorem testIso_baseAlongSquare (c : Comparison X Y)
    (f : R →ₐ[𝒪[K]] S) (g : S →ₐ[𝒪[K]] T)
    (p : R →ₐ[𝒪[K]] S') (q : S' →ₐ[𝒪[K]] T) (e : g.comp f = q.comp p)
    (A : CommAlgCat.{v} T)
    (b : (baseChangeAlongComparison (baseChangeAlongComparison c f) g).right.opens)
    (hb : IsUnit (algebraMap T A b.val))
    (b' : (baseChangeAlongComparison (baseChangeAlongComparison c p) q).right.opens)
    (hb' : IsUnit (algebraMap T A b'.val))
    (d : (baseChangeAlongComparison c (g.comp f)).right.opens)
    (hd : IsUnit (algebraMap T A d.val))
    (d' : (baseChangeAlongComparison c (q.comp p)).right.opens)
    (hd' : IsUnit (algebraMap T A d'.val)) (a : c.right.opens)
    (ha : IsUnit (algebraMap R (restrictCoefficientAlgebra (q.comp p) A) a.val))
    (x : ((X.baseChangeAlong p).baseChangeAlong q).atlas.opens)
    (y : ((Y.baseChangeAlong p).baseChangeAlong q).atlas.opens)
    (hx : IsUnit (algebraMap T A x.val)) (hy : IsUnit (algebraMap T A y.val)) :
    ((baseChangeAlongComparison (baseChangeAlongComparison c f) g).testIso A b hb
      (BasicAtlas.sourceChart (X.atlas.baseAlongSquareOpens_eq f g p q e) x)
      (BasicAtlas.sourceChart (Y.atlas.baseAlongSquareOpens_eq f g p q e) y) hx hy).trans
        ((Y.order.baseAlongSquareIso f g p q e).onChart A y hy) =
      ((X.order.baseAlongSquareIso f g p q e).onChart A x hx).trans
        ((baseChangeAlongComparison (baseChangeAlongComparison c p) q).testIso A b' hb' x y hx hy) := by
  let xq := BasicAtlas.sourceChart (X.atlas.baseAlongCompOpens_eq p q).symm x
  let yq := BasicAtlas.sourceChart (Y.atlas.baseAlongCompOpens_eq p q).symm y
  let xf := BasicAtlas.sourceChart (X.atlas.baseAlongEqOpens_eq e) xq
  let yf := BasicAtlas.sourceChart (Y.atlas.baseAlongEqOpens_eq e) yq
  have haf : IsUnit (algebraMap R (restrictCoefficientAlgebra (g.comp f) A) a.val) := by
    change IsUnit (algebraMap T A ((g.comp f) a.val))
    have hqa : IsUnit (algebraMap T A ((q.comp p) a.val)) := ha
    simpa only [e] using hqa
  have h₁ := testIso_baseAlongComp c f g A b hb d hd a haf xf yf hx hy
  have h₂ := testIso_baseAlongEq c e A d hd d' hd' xq yq hx hy
  have h₃ := testIso_baseAlongComp c p q A b' hb' d' hd' a ha xq yq hx hy
  have h := ModuleLaw.OrderAction.Iso.square_paste
    (ModuleLaw.OrderAction.Iso.square_paste h₁ h₂) (ModuleLaw.OrderAction.Iso.square_reverse h₃)
  simpa only [BasicAtlas.OrderAction.baseAlongSquareIso,
    BasicAtlas.OrderAction.Iso.onChart_trans, BasicAtlas.OrderAction.Iso.onChart_symm] using h

/-- Four specified actual rational test maps with their proved commuting coefficient square. -/
def baseAlongSquareTestSquare (c : Comparison X Y)
    (f : R →ₐ[𝒪[K]] S) (g : S →ₐ[𝒪[K]] T)
    (p : R →ₐ[𝒪[K]] S') (q : S' →ₐ[𝒪[K]] T) (e : g.comp f = q.comp p)
    (A : CommAlgCat.{v} T)
    (b : (baseChangeAlongComparison (baseChangeAlongComparison c f) g).right.opens)
    (hb : IsUnit (algebraMap T A b.val))
    (b' : (baseChangeAlongComparison (baseChangeAlongComparison c p) q).right.opens)
    (hb' : IsUnit (algebraMap T A b'.val))
    (d : (baseChangeAlongComparison c (g.comp f)).right.opens)
    (hd : IsUnit (algebraMap T A d.val))
    (d' : (baseChangeAlongComparison c (q.comp p)).right.opens)
    (hd' : IsUnit (algebraMap T A d'.val)) (a : c.right.opens)
    (ha : IsUnit (algebraMap R (restrictCoefficientAlgebra (q.comp p) A) a.val))
    (x : ((X.baseChangeAlong p).baseChangeAlong q).atlas.opens)
    (y : ((Y.baseChangeAlong p).baseChangeAlong q).atlas.opens)
    (hx : IsUnit (algebraMap T A x.val)) (hy : IsUnit (algebraMap T A y.val)) :=
  ModuleLaw.OrderAction.Iso.rationalSquare (F := K)
    ((baseChangeAlongComparison (baseChangeAlongComparison c f) g).testIso A b hb
      (BasicAtlas.sourceChart (X.atlas.baseAlongSquareOpens_eq f g p q e) x)
      (BasicAtlas.sourceChart (Y.atlas.baseAlongSquareOpens_eq f g p q e) y) hx hy)
    ((Y.order.baseAlongSquareIso f g p q e).onChart A y hy)
    ((X.order.baseAlongSquareIso f g p q e).onChart A x hx)
    ((baseChangeAlongComparison (baseChangeAlongComparison c p) q).testIso A b' hb' x y hx hy)
    (testIso_baseAlongSquare c f g p q e A b hb b' hb' d hd d' hd' a ha x y hx hy)

end Langlands.FormalGroup.LocalDivision.SpecialAtlas
