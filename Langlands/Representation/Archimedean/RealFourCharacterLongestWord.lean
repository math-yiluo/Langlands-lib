import Langlands.Representation.Archimedean.RealAmbientCanonicalCharacterBraid
import Langlands.Representation.Archimedean.RealBlockFrobeniusDisjoint

/-! # The two six-crossing words for reversal of four characters -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.RealFourCharacterLongestWord

open Langlands.LocalFactor.Archimedean RealStandardFiltration RealBlockFrobeniusMap
  RealCharacterPair RealCanonicalCharacterBraid

abbrev characters (x y u v : RealCharacterData) : List RealBlock :=
  [.character x, .character y, .character u, .character v]

abbrev Four (x y u v : RealCharacterData) := KF 4 (characters x y u v)

variable {x y u v : RealCharacterData}

/-- The canonical crossing in the first two positions. -/
def swap0 (c : Choice (pairParity x y)) : Four x y u v →ₗ[ℂ] Four y x u v :=
  crossing (n := 4) (pre := []) (post := [.character u, .character v]) rfl c

/-- The canonical crossing in the middle two positions. -/
def swap1 (c : Choice (pairParity y u)) : Four x y u v →ₗ[ℂ] Four x u y v :=
  crossing (n := 4) (pre := [.character x]) (post := [.character v]) rfl c

/-- The canonical crossing in the last two positions. -/
def swap2 (c : Choice (pairParity u v)) : Four x y u v →ₗ[ℂ] Four x y v u :=
  crossing (n := 4) (pre := [.character x, .character y]) (post := []) rfl c

private theorem braid01
    (hPoly : ∀ N a b, RealGenericCharacterBraidReduction.PolynomialBraid N a b)
    (cxy : Choice (pairParity x y)) (cyu : Choice (pairParity y u))
    (cxu : Choice (pairParity x u)) (h : cxu.parameter = cxy.parameter + cyu.parameter)
    (f : Four x y u v) :
    swap0 cyu (swap1 cxu (swap0 cxy f)) = swap1 cxy (swap0 cxu (swap1 cyu f)) :=
  LinearMap.congr_fun
    (RealAmbientCanonicalCharacterBraid.braid_of_polynomial (n := 4)
      (pre := []) (post := [.character v]) hPoly rfl cxy cyu cxu h) f

private theorem braid12
    (hPoly : ∀ N a b, RealGenericCharacterBraidReduction.PolynomialBraid N a b)
    (cyu : Choice (pairParity y u)) (cuv : Choice (pairParity u v))
    (cyv : Choice (pairParity y v)) (h : cyv.parameter = cyu.parameter + cuv.parameter)
    (f : Four x y u v) :
    swap1 cuv (swap2 cyv (swap1 cyu f)) = swap2 cyu (swap1 cyv (swap2 cuv f)) :=
  LinearMap.congr_fun
    (RealAmbientCanonicalCharacterBraid.braid_of_polynomial (n := 4)
      (pre := [.character x]) (post := []) hPoly rfl cyu cuv cyv h) f

private theorem commute02 (cxy : Choice (pairParity x y)) (cuv : Choice (pairParity u v))
    (f : Four x y u v) :
    swap2 cuv (swap0 cxy f) = swap0 cxy (swap2 cuv f) :=
  RealBlockFrobeniusDisjoint.blockFrobMap_disjoint_comm
    (data (n := 4) (pre := []) (post := [.character u, .character v]) rfl cxy)
    (data (n := 4) (pre := [.character y, .character x]) (post := []) rfl cuv)
    (data (n := 4) (pre := [.character x, .character y]) (post := []) rfl cuv)
    (data (n := 4) (pre := []) (post := [.character v, .character u]) rfl cxy)
    (Or.inl (show (0 : ℕ) + 1 < 2 by decide)) f

/-- The reversal words in chronological order `102102` and `021021` agree
when the six crossing parameters are additive on each triple. -/
theorem longestWord
    (hPoly : ∀ N a b, RealGenericCharacterBraidReduction.PolynomialBraid N a b)
    (cxy : Choice (pairParity x y)) (cxu : Choice (pairParity x u))
    (cxv : Choice (pairParity x v)) (cyu : Choice (pairParity y u))
    (cyv : Choice (pairParity y v)) (cuv : Choice (pairParity u v))
    (hxyu : cxu.parameter = cxy.parameter + cyu.parameter)
    (hxyv : cxv.parameter = cxy.parameter + cyv.parameter)
    (hxuv : cxv.parameter = cxu.parameter + cuv.parameter)
    (hyuv : cyv.parameter = cyu.parameter + cuv.parameter)
    (f : Four x y u v) :
    swap2 cxy (swap0 cuv (swap1 cxv (swap2 cyv (swap0 cxu (swap1 cyu f))))) =
    swap1 cyu (swap2 cxu (swap0 cyv (swap1 cxv (swap2 cuv (swap0 cxy f))))) := by
  calc
    _ = swap2 cxy (swap0 cuv (swap1 cxv (swap0 cxu (swap2 cyv (swap1 cyu f))))) := by
      rw [commute02 cxu cyv]
    _ = swap2 cxy (swap1 cxu (swap0 cxv (swap1 cuv (swap2 cyv (swap1 cyu f))))) := by
      rw [braid01 hPoly cxu cuv cxv hxuv]
    _ = swap2 cxy (swap1 cxu (swap0 cxv (swap2 cyu (swap1 cyv (swap2 cuv f))))) := by
      rw [braid12 hPoly cyu cuv cyv hyuv]
    _ = swap2 cxy (swap1 cxu (swap2 cyu (swap0 cxv (swap1 cyv (swap2 cuv f))))) := by
      rw [commute02 cxv cyu]
    _ = swap1 cyu (swap2 cxu (swap1 cxy (swap0 cxv (swap1 cyv (swap2 cuv f))))) := by
      rw [braid12 hPoly cxy cyu cxu hxyu]
    _ = swap1 cyu (swap2 cxu (swap0 cyv (swap1 cxv (swap0 cxy (swap2 cuv f))))) := by
      rw [braid01 hPoly cxy cyv cxv hxyv]
    _ = _ := by rw [commute02 cxy cuv]

end Langlands.Archimedean.RealFourCharacterLongestWord

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean RealCharacterPair RealCanonicalCharacterBraid
  RealFourCharacterLongestWord

/-- Conditional reversal for the two six-crossing words on an actual
four-character standard module. -/
def RealFourCharacterLongestWordStatement : Prop :=
  (∀ N a b, RealGenericCharacterBraidReduction.PolynomialBraid N a b) →
    ∀ (x y u v : RealCharacterData)
      (cxy : Choice (pairParity x y)) (cxu : Choice (pairParity x u))
      (cxv : Choice (pairParity x v)) (cyu : Choice (pairParity y u))
      (cyv : Choice (pairParity y v)) (cuv : Choice (pairParity u v)),
      cxu.parameter = cxy.parameter + cyu.parameter →
      cxv.parameter = cxy.parameter + cyv.parameter →
      cxv.parameter = cxu.parameter + cuv.parameter →
      cyv.parameter = cyu.parameter + cuv.parameter →
      ∀ f : Four x y u v,
        RealFourCharacterLongestWord.swap2 cxy
          (RealFourCharacterLongestWord.swap0 cuv (RealFourCharacterLongestWord.swap1 cxv
            (RealFourCharacterLongestWord.swap2 cyv (RealFourCharacterLongestWord.swap0 cxu
              (RealFourCharacterLongestWord.swap1 cyu f))))) =
        RealFourCharacterLongestWord.swap1 cyu
          (RealFourCharacterLongestWord.swap2 cxu (RealFourCharacterLongestWord.swap0 cyv
            (RealFourCharacterLongestWord.swap1 cxv (RealFourCharacterLongestWord.swap2 cuv
              (RealFourCharacterLongestWord.swap0 cxy f)))))

theorem realFourCharacterLongestWord : RealFourCharacterLongestWordStatement :=
  fun hPoly _ _ _ _ => longestWord hPoly

end Langlands.Archimedean
